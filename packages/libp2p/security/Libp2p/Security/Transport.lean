import Conc
import Streams
import Libp2p.Security.Constants
import Libp2p.Security.Handshake

/-!
# The Noise transport

After the handshake, each side holds two cipher states from `Split`:
one seals our messages, and one opens the peer's. Every transport
message is one frame: the 2-byte big-endian length, then the ciphertext
of at most `maxPlaintext` bytes and its 16-byte tag (the noise-libp2p
spec, "Wire Format"). The associated data is empty.

## The core

The transport is a pure core (root ARCHITECTURE §3.3), at the small
scale it has. `State` holds the two cipher states and the ciphertext of
a frame that has not fully arrived. `step` takes one event:

* `bytes`: the ciphertext of one post of the reader. The core opens
  every whole frame in the buffer, joins their plaintext, and keeps the
  rest.
* `write`: the plaintext of one application write, under a tag. The core
  seals it in chunks of `maxPlaintext` (owned contract 3).
* `eof`: the connection ended. An end between frames is orderly. An end
  inside a frame is `Error.truncatedFrame`, as go-libp2p's `io.ReadFull`
  fails with `io.ErrUnexpectedEOF` there
  (`vendor/go-libp2p/p2p/security/noise/rw.go`, lines 130 and 144).

A failed open is `Error.decrypt`, and a failed seal is an error too, so
the loop ends and tears the connection down (owned contracts 1 and 6).

## The shell

Three tasks run one secure connection, as the yamux shell runs a
session (`Yamux.Loop`):

* **The reader** reads the connection and posts `Event.bytes`. Before
  each post it takes a credit, so it never reads further ahead than the
  inbox has room for, and one frame more.
* **The loop** owns the `State`. It takes one event at a time, calls
  `step`, and performs the actions. Nothing it performs parks.
* **The writer** writes the sealed frames to the connection, in order,
  and answers a write's tag after its frames have gone.

## The reader's frames

The reader reads until its buffer holds at least one whole frame, and
then posts every whole frame of the buffer as one event. It keeps the
rest of the buffer for the next post. A connection read can split the
peer's frames at any byte, down to one byte per read. A post per read
would then cost one loop step and one credit per byte. The buffer holds
at most one frame that has not fully arrived, `2 + maxMessage` bytes,
and one read more (root §5.1). At the end of the connection the reader
posts the rest, so the core sees an end inside a frame
(`Error.truncatedFrame`).

The reader appends each read to a buffer that it alone holds, so Lean
grows the array in place, and the appends of a frame cost linear time.
The handshake's leftover seeds the buffer, so the frames it holds and
the frames of the reads line up.

## The credits

Noise has no window, so the read side keeps its bound through credits
(PRINCIPLES 3.4). The inbox holds `inboxChunks` chunks, and the credit
channel starts with as many tokens. The reader takes one token per
post. Each `bytes` event gives exactly one action that settles it
(`stepBytesSettles`): a `deliver` takes an inbox slot, and the reader
of the secure connection returns the token when it takes the chunk; a
`credit` returns the token at once, when the post opened no plaintext.
So the tokens, the posts in flight, and the chunks in the inbox always
add up to `inboxChunks`. A delivery always finds a free slot, and the
loop never parks on the inbox. While the application reads nothing, the
reader holds no token, and TCP carries the back-pressure to the peer.

## The ends

The loop ends in one of three ways: the owner closed the secure
connection, the connection ended, or `step` failed. `teardown` records
the answer and closes the event queue, the inbox, and the credits.
After a failure it closes the connection first, so a read sees the end
only after the teardown (owned contract 1). Then it closes the writer's
queue. The writer writes what the queue holds and answers each tag in
order, so a write never answers `closed` for frames that went out. Then
it closes the tag table, which answers the writes the loop never took,
and the connection.
-/

set_option autoImplicit false

namespace Libp2p.Security.Noise.Transport

-- `Conc` and `Streams` each define an `Error`, so the module opens the
-- names it uses, and `Error` stays `Noise.Error`.
open Conc (Async Chan OnceRef Outcome TaskSet)
open Streams (Connection Completions)
open Bytes (Blob)

/-! ## The core -/

/-- The state of one secure connection. -/
structure State where
  /-- The cipher state of our messages. -/
  send : CipherState
  /-- The cipher state of the peer's messages. -/
  recv : CipherState
  /-- The ciphertext of a frame that has not fully arrived. It holds
  less than one whole frame, so at most `2 + maxMessage` bytes. -/
  pending : Blob
  deriving BEq, Repr

/-- The state after a handshake. The leftover of the handshake seeds
the reader and arrives in its first `bytes` event, so the state starts
with no pending bytes. -/
def State.ofCompletion (c : Completion) : State :=
  ⟨c.send, c.recv, ⟨.empty⟩⟩

/-- An input of the transport core. -/
inductive Event where
  /-- The bytes of one post of the reader. -/
  | bytes (b : Blob)
  /-- The plaintext of one application write, under its tag. -/
  | write (tag : Nat) (pt : Blob)
  /-- The connection ended. -/
  | eof
  deriving BEq, Repr

/-- An output of the transport core. The shell performs the actions in
order. -/
inductive Action where
  /-- Write the sealed frames to the connection. -/
  | send (frames : Blob)
  /-- Answer the write of the tag: the frames before it have gone. -/
  | done (tag : Nat)
  /-- Hand the plaintext to the reader. It is never empty. -/
  | deliver (pt : Blob)
  /-- The read completed no frame with plaintext: the reader may read
  again. -/
  | credit
  /-- The connection ended: the loop ends. -/
  | shutdown
  deriving BEq, Repr

/-- The number of frames that carry `n` bytes of plaintext: `n` divided
by `maxPlaintext`, rounded up. An empty write takes no frame, as go and
nim send nothing for it. -/
def frameCount (n : Nat) : Nat :=
  (n + maxPlaintext - 1) / maxPlaintext

/-- Seal the plaintext as frames of at most `maxPlaintext` bytes each,
and join the frames (owned contract 3). One write gives one joined
buffer, so the writer puts its frames on the wire together, as nim does
("to avoid interleaving / sequencing issues",
`vendor/nim-libp2p/libp2p/protocols/secure/noise.nim`, line 523). -/
def sealFrames (cs : CipherState) (pt : ByteArray) : Except Error (CipherState × ByteArray) :=
  (List.range (frameCount pt.size)).foldlM (init := (cs, ByteArray.empty)) fun (cs, out) i => do
    let chunk := pt.extract (i * maxPlaintext) ((i + 1) * maxPlaintext)
    let (cs, ct) ← cs.encryptWithAd .empty chunk
    -- `ct` holds at most `maxPlaintext + 16 = maxMessage` bytes, so the
    -- frame always fits.
    let some frame := Streams.Framing.encodeB? .u16be maxMessage ct
      | throw (.messageTooLarge ct.size)
    return (cs, out ++ frame)

/-- Open every whole frame of `buf` from `pos` on, and join the
plaintext onto `out`. The answer holds the cipher state, the joined
plaintext, and the bytes of the frame that has not fully arrived.

The reads move `pos` and copy only the frame they open, so a buffer of
many small frames costs one pass. Each frame takes at least the 2 bytes
of its prefix, so `fuel` frames of a buffer of `2 * fuel` bytes or less
cover it; `openFrames` passes that fuel. -/
private def openFrom (cs : CipherState) (buf : ByteArray) :
    Nat → Nat → ByteArray → Except Error (CipherState × ByteArray × ByteArray)
  | 0, pos, out => .ok (cs, out, buf.extract pos buf.size)
  | fuel + 1, pos, out =>
    -- The header comes out of a 2-byte window, so the parse copies 2
    -- bytes however much the buffer holds.
    match Streams.Framing.headerB? .u16be maxMessage (buf.extract pos (pos + 2)) with
    | .error .truncated => .ok (cs, out, buf.extract pos buf.size)
    -- `maxMessage` is the largest length two bytes carry, so no header
    -- is over the cap. The arm keeps the match total.
    | .error .malformed => .error (.messageTooLarge (buf.size - pos))
    | .ok (len, size) =>
      let start := pos + size
      if buf.size < start + len then .ok (cs, out, buf.extract pos buf.size)
      else do
        let (cs, pt) ← cs.decryptWithAd .empty (buf.extract start (start + len))
        openFrom cs buf fuel (start + len) (out ++ pt)

/-- Open every whole frame of `buf`: the cipher state, the joined
plaintext, and the rest. -/
def openFrames (cs : CipherState) (buf : ByteArray) :
    Except Error (CipherState × ByteArray × ByteArray) :=
  openFrom cs buf (buf.size / 2 + 1) 0 .empty

/-- The end of the whole frames of `buf` from `pos`: the offset after
the last frame whose 2-byte length and ciphertext are all in `buf`. The
scan reads only the length prefixes. Each frame takes at least 2 bytes,
so a `fuel` of `buf.size / 2 + 1` reaches the end (`wholeFrames`). -/
def wholeFramesFrom (buf : ByteArray) : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos =>
    if h : pos + 2 ≤ buf.size then
      -- The `u16be` prefix of the noise-libp2p spec, "Wire Format".
      let len := buf[pos].toNat * 256 + buf[pos + 1].toNat
      if pos + 2 + len ≤ buf.size then wholeFramesFrom buf fuel (pos + 2 + len) else pos
    else pos

/-- The length of the longest prefix of `buf` that holds whole frames
only. The reader posts that prefix (module doc, "The reader's
frames"). -/
def wholeFrames (buf : ByteArray) : Nat :=
  wholeFramesFrom buf (buf.size / 2 + 1) 0

/-- The scan never passes the end of the buffer. -/
theorem wholeFramesFromLe (buf : ByteArray) :
    ∀ (fuel pos : Nat), pos ≤ buf.size → wholeFramesFrom buf fuel pos ≤ buf.size
  | 0, _, h => h
  | fuel + 1, pos, h => by
    unfold wholeFramesFrom
    split
    -- The `let` of the length hides the inner `if` from `split`, so
    -- `dsimp only` substitutes the binding first.
    · dsimp only
      split
      · next hn => exact wholeFramesFromLe buf fuel _ hn
      · exact h
    · exact h

/-- The prefix of whole frames fits in the buffer, so the reader's
`extract` calls cut inside it. -/
theorem wholeFramesLe (buf : ByteArray) : wholeFrames buf ≤ buf.size :=
  wholeFramesFromLe buf _ 0 (Nat.zero_le _)

-- One frame of 1 byte, then a frame of 2 bytes with 1 arrived.
#guard wholeFrames ⟨#[0, 1, 9, 0, 2, 7]⟩ == 3
-- One frame of 1 byte, then an empty frame: both are whole.
#guard wholeFrames ⟨#[0, 1, 9, 0, 0]⟩ == 5
-- Half a length prefix.
#guard wholeFrames ⟨#[0]⟩ == 0

/-- The action that settles one post: the plaintext, or a credit when
the post gave none. A frame may carry an empty plaintext, and the last
post may hold the rest of a frame only. The inbox takes no empty chunk,
so an empty result returns the credit. -/
def settle (pt : ByteArray) : Action :=
  if pt.isEmpty then .credit else .deliver ⟨pt⟩

/-- The transition function. -/
def step (st : State) : Event → Except Error (State × List Action)
  | .bytes b => do
    let (recv, pt, rest) ← openFrames st.recv (st.pending.bytes ++ b.bytes)
    return ({ st with recv, pending := ⟨rest⟩ }, [settle pt])
  | .write tag pt => do
    let (send, frames) ← sealFrames st.send pt.bytes
    let acts := if frames.isEmpty then [.done tag] else [.send ⟨frames⟩, .done tag]
    return ({ st with send }, acts)
  | .eof =>
    -- An end inside a frame breaks the stream (`Error.truncatedFrame`).
    if st.pending.bytes.isEmpty then return (st, [.shutdown])
    else throw (.truncatedFrame st.pending.bytes.size)

/-- A `bytes` event that succeeds gives exactly one action, and it
settles the read: a delivery or a credit. The credit count of the shell
rests on this. -/
theorem stepBytesSettles (st st' : State) (b : Blob) (acts : List Action)
    (h : step st (.bytes b) = .ok (st', acts)) :
    acts = [.credit] ∨ ∃ p, acts = [.deliver p] := by
  simp only [step] at h
  -- The `do` block binds the result of `openFrames`; a case split on it
  -- lets `Except.bind` reduce.
  cases hx : openFrames st.recv (st.pending.bytes ++ b.bytes) with
  | error e => simp [hx, bind, Except.bind] at h
  | ok x =>
    simp only [hx, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    unfold settle
    split
    · exact .inl rfl
    · exact .inr ⟨_, rfl⟩

/-! ## The shell -/

/-- An item for the writer. -/
inductive Out where
  /-- Write the frames. -/
  | frames (bytes : ByteArray)
  /-- Answer the write of the tag: the frames before it have gone. -/
  | done (tag : Nat)

/-- How the loop ended. -/
inductive Ending where
  /-- The owner closed the secure connection. -/
  | closed
  /-- The connection ended. -/
  | shutdown
  /-- `step` failed. -/
  | failed (e : Error)

/-- The parts of a secure connection that its tasks and its surface
share. Each one is a channel, a tag table, or a cell, so a task changes
them only through their atomic operations. -/
structure Shared where
  /-- The connection under the secure connection. -/
  conn : Connection
  /-- The events for the loop. -/
  events : Chan Event
  /-- The writer's queue. It has no capacity limit: each item belongs
  to a write whose writer waits on its tag, so the writers bound it, as
  in the yamux shell. -/
  out : Chan Out
  /-- The plaintext for the reader of the secure connection. -/
  inbox : Chan ByteArray
  /-- The reader's credits (module doc, "The credits"). -/
  credits : Chan Unit
  /-- The tags of the writes. -/
  writes : Completions Unit
  /-- The answer, once the loop has ended, the first fault of a
  connection read while the loop ran, and the first failed write. -/
  outcome : Outcome Error

namespace Shared

/-- Perform one action. The answer is true for `shutdown`. No action
parks: the writer's queue has no limit, and the credits keep a free
inbox slot for each delivery (module doc). -/
def perform (sh : Shared) : Action → BaseIO Bool
  | .send f => do
    discard <| sh.out.trySend (.frames f.bytes)
    return false
  | .done tag => do
    discard <| sh.out.trySend (.done tag)
    return false
  | .deliver p => do
    discard <| sh.inbox.trySend p.bytes
    return false
  | .credit => do
    discard <| sh.credits.trySend ()
    return false
  | .shutdown => return true

/-- The loop: take an event, step, perform, until the connection
ends. -/
def run (sh : Shared) (st : State) : Async Ending := do
  let mut st := st
  repeat
    -- Park: an event wakes it, and so does the close of the queue by
    -- `close` or by `teardown`.
    match ← sh.events.recv with
    | none => return .closed
    | some ev =>
      match step st ev with
      | .error e => return .failed e
      | .ok (st', acts) =>
        st := st'
        let mut stop := false
        for a in acts do
          if ← sh.perform a then stop := true
        if stop then return .shutdown
  return .closed

/-- End the secure connection: record the answer, and close every wait
it knows (module doc, "The ends"). -/
def teardown (sh : Shared) (ending : Ending) : BaseIO Unit := do
  sh.outcome.finish (match ending with | .failed e => .error e | _ => .ok ())
  -- A failure tears the connection down before a read sees the end
  -- (owned contracts 1 and 6).
  if let .failed _ := ending then sh.conn.closeQuietly
  sh.events.close
  -- The write tags stay open: the writer answers each one whose frames
  -- it holds, after it has written them, and closes the table when it
  -- ends.
  sh.inbox.close
  sh.credits.close
  sh.out.close

/-- The reader task (module doc, "The reader's frames"). `seed` holds
the handshake's leftover. Before each post it takes a credit, which the
loop or the application returns (module doc, "The credits"). It reads
until the buffer holds a whole frame, and posts every whole frame. A
failed read reaches `recordFault` and ends the reads like the end of
the connection. The task ends when the credits close, when a post
answers `.error` (the loop has ended), or at the end of the
connection. -/
def reader (sh : Shared) (seed : ByteArray) : Async Unit := do
  let mut buf := seed
  repeat
    -- Park: the loop or the application returns a credit, and the
    -- teardown closes the credits.
    if (← sh.credits.recv).isNone then break
    let mut cut := wholeFrames buf
    let mut ended := false
    while cut == 0 && !ended do
      -- Park: the peer's bytes wake it, and so does the close of the
      -- connection.
      match ← (try sh.conn.read catch e => do sh.outcome.recordFault e; pure none) with
      | some b =>
        -- `buf` has no other reference, so the append grows it in place.
        buf := buf ++ b
        cut := wholeFrames buf
      | none => ended := true
    if ended then
      -- The rest of a frame goes first, so the core sees the end inside
      -- it (`Error.truncatedFrame`).
      if !buf.isEmpty then
        if let .error _ ← sh.events.send (.bytes ⟨buf⟩) then break
      discard <| sh.events.send .eof
      break
    if let .error _ ← sh.events.send (.bytes ⟨buf.extract 0 cut⟩) then break
    buf := buf.extract cut buf.size

/-- The writer task. It answers each tag after the frames before it, so
a write answers `.ok` exactly when its frames have gone to the
connection. After a failed write the connection is torn down
(`Connection.write`), so the writer stops writing and answers the tags
with `closed`. The reader then sees the end, and the loop ends. When
the queue ends, the writer closes the tag table, which answers the
writes that the loop never took, and then the connection.

The failed write throws to its caller through `Session.write`, so the
writer records it as a failed write (`recordWriteFault`), which the
join does not throw. The caller decides what the failure means: the
yamux shell drops it after the peer's go-away, as go-yamux does
(`Yamux.Shared.recordWriteFault`). A fault of its own in the join would
override that decision, and a peer's orderly close would reach the
owner as a fault. -/
def writer (sh : Shared) : Async Unit := do
  let mut broken := false
  repeat
    -- Park: the loop's next item wakes it, and so does `teardown`.
    match ← sh.out.recv with
    | none => break
    | some (.frames b) =>
      if !broken then
        -- Park: the peer's reads wake the write, and so does the close
        -- of the connection.
        try sh.conn.write b catch e =>
          -- The caller of the write gets the failure (doc above).
          sh.outcome.recordWriteFault e
          broken := true
    | some (.done tag) =>
      sh.writes.resolve tag (if broken then .error .closed else .ok ())
  sh.writes.closeAll
  sh.conn.close

end Shared

/-- The fault of an operation on a secure connection that has ended. -/
private def closedError : IO.Error :=
  .resourceVanished 0 "noise: the secure connection is closed"

/-- A running secure connection: the surface that the seam value wraps
as a `SecureConn`. -/
structure Session where
  /-- The next plaintext chunk, never empty. `none` at the end. -/
  read : Async (Option ByteArray)
  /-- Seal and write the bytes, and return once the frames have gone to
  the connection. A failure throws, after the teardown. -/
  write : ByteArray → Async Unit
  /-- Close the secure connection and the connection under it. -/
  close : IO Unit
  /-- Wait until the tasks have ended, and answer how the connection
  ended: `.ok ()` for an orderly end, the `Noise.Error` for a broken
  peer. A fault of a connection read throws. A failed write reached its
  caller through `write`, and the join does not throw it again. -/
  join : Async (Except Error Unit)

namespace Session

/-- Run a secure connection over `conn` with the cipher states of the
handshake. `leftover` holds the ciphertext the handshake read past its
last message; it seeds the reader, ahead of any connection read
(owned contract 5). -/
def new (conn : Connection) (c : Completion) (leftover : ByteArray) : BaseIO Session := do
  let sh : Shared := {
    conn
    events := ← Chan.new eventQueueCap
    out := ← Chan.newUnbounded
    inbox := ← Chan.new inboxChunks
    credits := ← Chan.new inboxChunks
    writes := ← Completions.new
    outcome := ← Outcome.new }
  -- The credit queue is empty, so each send takes.
  for _ in [0:inboxChunks] do
    discard <| sh.credits.trySend ()
  let tasks ← TaskSet.new
  tasks.spawn do
    let ending ← sh.run (State.ofCompletion c)
    sh.teardown ending
  tasks.spawn sh.writer
  -- The leftover seeds the reader's buffer, ahead of every read, so its
  -- frames come first (module doc, "The reader's frames").
  tasks.spawn (sh.reader leftover)
  return {
    read := do
      -- Park: the loop's delivery wakes it, and so does `teardown`.
      match ← sh.inbox.recv with
      | some b =>
        -- The chunk has left the inbox: its slot is free again.
        discard <| sh.credits.trySend ()
        return some b
      | none => return none
    write := fun b => do
      let fail : Async Unit := do
        -- `Connection.write`: the connection is torn down before the
        -- throw.
        sh.conn.closeQuietly
        throw closedError
      let some (tag, slot) ← sh.writes.register | fail
      if let .error _ ← sh.events.send (.write tag ⟨b⟩) then
        sh.writes.resolve tag (.error .closed)
        fail
      -- Park: the writer answers the tag, and `teardown` closes the
      -- slot.
      match ← slot.recv with
      | some (.ok ()) => return ()
      | _ => fail
    -- The close of the connection wakes the reader and a parked write;
    -- the close of the queue ends the loop. The mark comes first: a
    -- read or a write that the close breaks is no fault
    -- (`Conc.Outcome`, "The owner's close").
    close := do
      sh.outcome.markClosing
      sh.events.close
      sh.conn.close
    -- A fault of a read under a clean answer throws (§3.5).
    join := do
      tasks.joinAll
      sh.outcome.answer }

end Session

end Libp2p.Security.Noise.Transport
