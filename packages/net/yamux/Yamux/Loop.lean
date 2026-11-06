import Std.Data.HashMap
import Streams
import Yamux.Core

/-!
# The loop: the IO shell of the core

One session runs three tasks (ARCHITECTURE §3.3):

* **The reader** turns each connection read into `Event.bytes`, and the
  end of the connection into `Event.eof`. It posts to the bounded event
  queue, and it holds one credit, so it reads one read ahead of the
  loop at most. A slow loop slows the reader, and TCP carries the
  back-pressure to the peer.
* **The loop** owns the core `State`. It takes one event at a time,
  calls `step`, and performs the actions. Nothing it performs parks: a
  frame goes to the writer's queue, bytes go to a free slot of a
  stream's bounded inbox (the core holds them while none is free), and
  an answer goes to a tag's slot. So the loop always comes back for the
  next event, and the reader never waits on a write.
* **The writer** takes the frames off its queue, in order, and writes
  them to the connection. It answers a write's tag only after the frame
  before the tag has gone to the connection, so back-pressure stays
  exact (§5.1). It is the one task that parks on the peer, and each
  write has a deadline (`writeDeadlineMs`): a peer that stops reading
  ends the session with a fault, as go-yamux ends it (the package
  ARCHITECTURE, "Checked against the implementations").

## The writer's queue

The queue is one FIFO, so the frames keep the order the core gave them.
It has no capacity limit, and the reason is the bound of each kind of
item. A data frame and the `done` marker after it belong to a write
whose writer waits on the tag, so the writers bound them. The frames
that a local operation causes (a SYN, a FIN, an RST, a window update)
come at most one per operation. The frames that the peer causes are the
control frames, and a counter holds them to `controlQueueCap` (owned
contract 5):

* the echo of a ping: beyond the cap the loop drops it, since the peer
  can ping again. go-yamux drops a pong the same way
  (`vendor/go-yamux/session.go`, lines 803 to 806).
* the answer to a SYN, the ACK or the RST the spec demands: the loop
  never drops it. The spec makes the receiver answer every SYN ("The
  receiver must then reply", `vendor/specs/yamux/README.md`, line 114),
  and the peer sends no SYN twice, so the answer is no frame "a peer
  can re-derive or re-request" (owned contract 5). Beyond the cap the
  loop takes no further event until the writer has sent enough of
  them, so the reader keeps its credit back and TCP slows the peer.
  go-yamux blocks its receive loop the same way: it sends the RST
  through `sendMsg` (`vendor/go-yamux/session.go`, line 884), which blocks while its
  send queue is full (line 536). One read can carry many SYN frames, so
  the queue holds at most the cap plus one read's worth of answers. The
  wait ends when the writer catches up, or at the write deadline, when
  the writer closes the connection and the signal.

## The reader's credit

The bytes of a read count against no window until the core has stepped
them. The event queue alone would let the reader run `eventQueueCap`
reads ahead of the loop: 64 reads of up to 64 KiB (`tcpReadChunk` of
`net/streams`), so 4 MiB of a connection that no window bounds.
The Go node of the interop target runs go-yamux with no read buffer of
its own, so go-yamux reads from the Noise session, which holds one
decrypted message ahead. The Noise transport of the layer above holds
its reader to one read the same way. The package ARCHITECTURE
("Decisions", the reader) cites both sources. So the reader
takes a credit before each read. The loop returns it after the step of
the bytes, and after the back-pressure wait of the SYN answers. Then
one read of the peer's bytes at
most waits outside the windows, and the rest stays in the connection,
where TCP slows the peer. The leftover of the negotiation is a read of
its own, and it holds the first credit.

## The parked writers

The core holds no parked write (owned contract 4). A write posts its
bytes. The core sends what the credit covers, and answers `done`, or
`blocked` with the count it sent. On `blocked`, the loop counts the
writer as parked on its stream, and the writer parks on the stream's
credit channel with the rest. On `credit`, the loop sends one token,
and only while a writer is parked; the writer it wakes posts its rest.
When that write completes with credit left, the core signals `credit`
again, and the next parked writer wakes. The loop counts and sends in
the order of the actions, so no token goes out before its writer is
counted, and no wakeup is lost. The end of the write direction closes
the credit channel (owned contract 7), and every parked writer wakes
with the reason.

## The reset

A reset ends the reads at once. The spec: "Reset a stream
immediately". So the shell drops the chunks the reader has not taken,
and the next read answers `.error .reset`. go-yamux answers a read
after the reset with the error and leaves its buffer unread (`Read`,
`vendor/go-yamux/stream.go`, lines 105 and 106), and nim clears its
queues (the package ARCHITECTURE, "Checked against the
implementations"). An RST after the peer's FIN leaves
the reads alone: the FIN ended them, the core keeps their EOF behind
the bytes it still holds (`Entry.onFrame`), and the RST ends the write
direction only. go-yamux and rust-yamux do the same (the package
ARCHITECTURE, "Checked against the implementations").

## The ticks

Time reaches the core as `Event.tick` (ARCHITECTURE, "Decisions"). The
ticker task posts one at each deadline the core asked for with
`Action.wakeAt`, and sleeps in between on the session's `Clock`, so
nothing polls. The reader posts a tick right before the bytes of each
read, and `Session.ping` right before its ping, so the core knows the
time at which a timer starts (`Yamux/Core.lean`, "Time"). A keepalive
that no pong answers ends the session with a `timeExpired` fault and no
go-away, as go-yamux closes it (`vendor/go-yamux/session.go`, line
470).

## The ends of a session

The loop ends in one of three ways, and `teardown` acts on each:

* the owner closed the session: a normal go-away goes out last;
* the peer ended it, by its normal go-away or by the end of the
  connection;
* `step` reported a `ProtocolError`: a go-away with the protocol-error
  code goes out last, and the error reaches the owner through the
  session completion (§3.5).

`teardown` closes every wait that the session knows: the event queue,
the reader's credit, the open tags, the write attempts, every credit
channel, every stream inbox, and the accept queue. Then it closes
the writer's queue. The writer writes what the queue holds, and answers
each write and ping tag in order, so a write never answers `closed` for
a frame that went out. Then it closes the write tags, which answers the
writes the loop never took, and the connection, which wakes the
reader. A peer that stops
reading holds the flush for one write deadline at most: the expiry
closes the connection, and the writer writes nothing more. An owner
that needs a shorter bound runs the join under `withinDeadline` and
closes the connection on expiry (PRINCIPLES 3.1).
-/

set_option autoImplicit false

namespace Yamux

open Conc Streams

/-- An item for the writer. -/
inductive Out where
  /-- Write the bytes. `control` marks a frame that the control counter
  holds. -/
  | frame (bytes : ByteArray) (control : Bool)
  /-- Answer the write or the ping of the tag: the frames before it have
  gone to the connection. -/
  | done (tag : Nat)

/-- The inbox of each live stream, by id. The loop alone holds it. -/
abbrev Inboxes := Std.HashMap Nat (Chan (Except Streams.Error ByteArray))

/-- The write side of one stream in the shell (owned contracts 4 and 7).
The writers that wait for credit park on `credit`, and the loop counts
them in `parked`. The loop sends a token only while a writer waits, so
the channel holds at most one token per parked writer. That count has
no bound of its own, so the channel is unbounded (ARCHITECTURE §4.1,
the named exception): the writers bound it, each by its own park. -/
structure WritePort where
  /-- The wake tokens. The loop closes it when the write direction
  ends, which wakes every parked writer. -/
  credit : Chan Unit
  /-- Why the write direction ended, set before `credit` closes. -/
  ended : OnceRef (Option Streams.Error)

/-- The write side of each stream whose write direction is open, by id,
with the count of its parked writers. The loop alone holds it. -/
abbrev Writers := Std.HashMap Nat (WritePort × Nat)

/-- End the write direction of a write side with `e`: record why, and
close the credit channel, which wakes every parked writer. -/
def WritePort.finish (wp : WritePort) (e : Streams.Error) : BaseIO Unit := do
  wp.ended.update fun w => w <|> some e
  wp.credit.close

/-- The shell's side of the live streams: the inboxes, and the write
side of each stream whose write direction is open. The loop alone holds
it. -/
structure Ports where
  /-- The inbox of each stream that still reads. -/
  inboxes : Inboxes := {}
  /-- The write side of each stream that still writes. -/
  writers : Writers := {}

/-- Add the new stream `id` to the ports. -/
def Ports.add (p : Ports) (id : Nat) (inbox : Chan (Except Streams.Error ByteArray))
    (wp : WritePort) : Ports :=
  { inboxes := p.inboxes.insert id inbox, writers := p.writers.insert id (wp, 0) }

/-- The answer to one attempt of a write: `none` when the core took the
rest of the bytes, `some n` when it took the first `n` and the writer
parks. -/
abbrev Attempt := Except Streams.Error (Option Nat)

/-- The open attempts of the writes, by the write's tag, with the slot
each one waits on, and whether the table is closed. A write makes one
attempt at a time, so its tag names the attempt. -/
abbrev Attempts := OnceRef (Std.HashMap Nat (Chan Attempt) × Bool)

/-- How a loop ended. -/
inductive Ending where
  /-- The owner closed the session. -/
  | closed
  /-- The peer ended the session: a normal go-away, or the end of the
  connection. -/
  | shutdown
  /-- The core reported a protocol error. -/
  | failed (e : ProtocolError)

/-- The parts of a session that its tasks and its surface share. Each
one is a channel, a tag table, or a cell, so a task changes them only
through their atomic operations. -/
structure Shared where
  /-- The connection under the session. -/
  conn : Connection
  /-- The clock of the write deadline. -/
  clock : Clock
  /-- The events for the loop. -/
  events : Chan Event
  /-- The writer's queue. -/
  out : Chan Out
  /-- The control frames in the writer's queue: ping echoes and SYN
  answers. -/
  controlCount : OnceRef Nat
  /-- The writer's signal that it sent a control frame. It has room for
  one token, and the writer closes it when it ends. -/
  room : Chan Unit
  /-- The tags of writes and pings. -/
  writes : Completions Unit
  /-- The open attempts of the writes. -/
  attempts : Attempts
  /-- The tags of opens; the answer is the stream. -/
  opens : Completions Stream
  /-- The inbound streams that wait for `acceptStream`. -/
  accepts : Chan Stream
  /-- The reader's credit (module doc, "The reader's credit"). It has
  room for one token, and the teardown closes it. -/
  credits : Chan Unit
  /-- The time of the next tick the core asked for, and its signal
  (module doc, "The ticks"); the teardown closes it. -/
  alarm : Alarm
  /-- The answer of the session, and the first fault of the connection
  while it ran: a read fault, a write past the write deadline, or a
  keepalive with no pong. -/
  outcome : Outcome ProtocolError
  /-- The peer's normal go-away ended the session. -/
  peerGoAway : OnceRef Bool
  /-- The owner's close ended the session: the loop found its event
  queue closed. -/
  ownerEnded : OnceRef Bool

namespace Shared

/-- Record a failed write to the connection, on the terms of
`Outcome.recordFault`. It reaches `join` unless the peer's go-away or
the owner's close ended the session. go-yamux makes the same two
choices. Its send loop prefers the receive loop's go-away to its own
write error, and it keeps the error only when no close came first: the
owner's `Close` sets `shutdownErr`, and the send loop then changes
nothing (`vendor/go-yamux/session.go`, lines 283 to 306 and 545 to
566). Both owners can close at once, and the peer's close can fail our
write before our loop reads its go-away, so the owner's close needs the
rule as well. A session that ends by itself, at the end of the
connection, still reports the failed write. -/
def recordWriteFault (sh : Shared) (e : IO.Error) : BaseIO Unit :=
  sh.outcome.recordWriteFault e

/-! ## The write attempts -/

/-- Open the attempt of the write `tag`: its slot, or `none` once the
table is closed. -/
def openAttempt (sh : Shared) (tag : Nat) : BaseIO (Option (Chan Attempt)) := do
  let slot : Chan Attempt ← Chan.new 1
  sh.attempts.updateGet fun (m, closed) =>
    if closed then (none, (m, closed)) else (some slot, (m.insert tag slot, closed))

/-- Answer the attempt of the write `tag`. An unknown tag does nothing:
a ping's tag, or a write that made no attempt. -/
def answerAttempt (sh : Shared) (tag : Nat) (a : Attempt) : BaseIO Unit := do
  let slot ← sh.attempts.updateGet fun (m, closed) => (m.get? tag, (m.erase tag, closed))
  if let some slot := slot then
    -- The slot has room for this one answer, so the send never parks.
    discard <| slot.trySend a
    slot.close

/-- Close the attempts: each waiting write wakes with no answer. -/
def closeAttempts (sh : Shared) : BaseIO Unit := do
  let slots ← sh.attempts.updateGet fun (m, _) => (m.toList, ({}, true))
  for (_, slot) in slots do
    slot.close

/-- Write `b` under `tag` on the stream `key` with the write side `wp`,
attempt by attempt (module doc, "The parked writers"). The answer of the
write itself goes to `tag` in `sh.writes`: the writer task sends it once
the frames have gone, or this function sends it when the write cannot
go on. `.error` means that the loop has ended and took no answer. -/
def postWrite (sh : Shared) (key : StreamKey) (wp : WritePort) (tag : Nat) (b : ByteArray) :
    Async (Except Conc.Error Unit) := do
  -- A write direction that ended answers with its reason at once: after
  -- a reset the core has retired the stream and would answer `closed`.
  if let some why ← (wp.ended.get : BaseIO (Option Streams.Error)) then
    sh.writes.resolve tag (.error why)
    return .ok ()
  let mut rest := b
  repeat
    let some slot ← sh.openAttempt tag | return .error .closed
    if let .error _ ← sh.events.send (.write key tag ⟨rest⟩) then
      sh.answerAttempt tag (.error .closed)
      return .error .closed
    -- Park: the loop answers the attempt, and the teardown closes it.
    match ← slot.recv with
    | none => return .error .closed
    | some (.error _) => return .ok ()
    | some (.ok none) => return .ok ()
    | some (.ok (some n)) =>
      rest := rest.extract n rest.size
      -- Park: a credit token wakes it, and the end of the write
      -- direction closes the channel.
      if (← wp.credit.recv).isNone then
        let why := ((← (wp.ended.get : BaseIO (Option Streams.Error))).getD .closed)
        sh.writes.resolve tag (.error why)
        return .ok ()
  return .ok ()

/-! ## Streams and actions -/

/-- A new stream `id`: its inbox, its write side, and the stream that
reads and writes them. The inbox is the bounded `Chan` of ARCHITECTURE
§3.3: `inboxChunks` slots for data and one for the reset or the end of
the session. The core counts the data slots (`StreamState.slots`): it
delivers only into a free slot, and holds the rest, so a delivery
always fits and never parks the loop. A read frees its slot before it
posts the count. -/
def newStream (sh : Shared) (key : StreamKey) :
    BaseIO (Stream × Chan (Except Streams.Error ByteArray) × WritePort) := do
  let inbox ← Chan.new (inboxChunks + 1) (by simp)
  let wp : WritePort := { credit := ← Chan.newUnbounded, ended := ← OnceRef.new none }
  -- The port posts under the key, so after the stream retires its events
  -- reach no later stream on the same id (`stepStale`).
  let port : LoopPort := {
    inbox
    completions := sh.writes
    postWrite := sh.postWrite key wp
    postConsumed := fun n => sh.events.send (.consumed key n)
    postClose := sh.events.send (.close key)
    postReset := sh.events.send (.reset key) }
  return (← Stream.ofPort port, inbox, wp)

/-- Queue a frame for the writer. The queue has no limit, so the send
never parks (module doc). -/
def queue (sh : Shared) (item : Out) : BaseIO Unit :=
  discard <| sh.out.trySend item

/-- Perform one action, other than `accept`, which needs the state
(`performAll`). -/
def performOne (sh : Shared) (p : Ports) : Action → BaseIO Ports
  | .send f => do
    sh.queue (.frame f.bytes false)
    return p
  | .control f => do
    -- A ping echo: take a place under the cap, or drop the frame.
    let room ← sh.controlCount.updateGet fun n =>
      if n < controlQueueCap then (true, n + 1) else (false, n)
    if room then sh.queue (.frame f.bytes true)
    return p
  | .reply f => do
    -- A SYN answer always goes; `run` pauses while too many wait.
    sh.controlCount.update (· + 1)
    sh.queue (.frame f.bytes true)
    return p
  | .deliver id b => do
    if let some inbox := p.inboxes.get? id then discard <| inbox.trySend (.ok b.bytes)
    return p
  | .eof id => do
    if let some inbox := p.inboxes.get? id then inbox.close
    return { p with inboxes := p.inboxes.erase id }
  | .reset id => do
    if let some inbox := p.inboxes.get? id then
      -- The reset ends the reads at once: the unread chunks go, and the
      -- next read answers `.reset` (module doc, "The reset").
      discard inbox.drain
      discard <| inbox.trySend (.error .reset)
      inbox.close
    return { p with inboxes := p.inboxes.erase id }
  | .accept _ => return p
  | .opened tag key => do
    let (stream, inbox, wp) ← sh.newStream key
    sh.opens.resolve tag (.ok stream)
    return p.add key.id inbox wp
  | .openRefused tag e => do
    sh.opens.resolve tag (.error e)
    return p
  | .done tag => do
    -- The writer answers the tag once the frames before it have gone;
    -- the attempt ends now.
    sh.queue (.done tag)
    sh.answerAttempt tag (.ok none)
    return p
  | .blocked id tag n => do
    -- Count the writer as parked before it can take a token.
    sh.answerAttempt tag (.ok (some n))
    match p.writers.get? id with
    | some (wp, parked) => return { p with writers := p.writers.insert id (wp, parked + 1) }
    | none => return p
  | .credit id => do
    -- One token, and only while a writer is parked (owned contract 4).
    match p.writers.get? id with
    | some (wp, parked + 1) =>
      discard <| wp.credit.trySend ()
      return { p with writers := p.writers.insert id (wp, parked) }
    | _ => return p
  | .endWrites id e => do
    if let some (wp, _) := p.writers.get? id then wp.finish e
    return { p with writers := p.writers.erase id }
  | .refused tag e => do
    sh.writes.resolve tag (.error e)
    sh.answerAttempt tag (.error e)
    return p
  | .wakeAt t => do
    sh.alarm.set t
    return p
  | .expired => do
    sh.outcome.recordFault (.timeExpired 0 s!"yamux: no pong answered the keepalive within {pingDeadlineMs} ms")
    return p
  | .shutdown => return p

/-- Perform the actions of one step, in order. The answer holds the
state and the ports after them, and whether the session shuts down.

An `accept` offers the new stream to the accept queue. The queue holds
`backlogCap` streams, as many as the core lets the peer open; a stream
the peer reset before the application took it still holds its place. A
stream that finds the queue full is reset at once, through the core,
so the peer learns of it and the table forgets it.

A step that resets a stream skips the deliveries of that step to the
stream. The reset would drain those chunks unread, but the reader runs
beside the loop, and could take one between the delivery and the
drain. So the reset ends the reads at the point of its step, in every
order of the two tasks (module doc, "The reset"). A step that also ends
the reads with EOF keeps its deliveries: the EOF retires the inbox, and
a reset after the peer's FIN leaves the reads at EOF. -/
def performAll (sh : Shared) (st : State) (p : Ports) (acts : List Action) :
    BaseIO (State × Ports × Bool) := do
  let mut st := st
  let mut p := p
  let mut stop := false
  let resets := acts.filterMap fun | .reset id => some id | _ => none
  let eofs := acts.filterMap fun | .eof id => some id | _ => none
  for a in acts do
    match a with
    | .deliver id _ =>
      if !(resets.contains id && !eofs.contains id) then p ← sh.performOne p a
    | .accept key =>
      let (stream, inbox, wp) ← sh.newStream key
      if ← sh.accepts.trySend stream then
        p := p.add key.id inbox wp
      else
        -- A reset of a live stream cannot fail, and it accepts nothing.
        -- The core put the ACK before the offer, so the RST follows it.
        if let .ok (st', more) := step st (.reset key) then
          st := st'
          for m in more do
            p ← sh.performOne p m
    | .shutdown =>
      stop := true
    | .expired =>
      -- The fault reaches `join`; the session ends with no go-away.
      p ← sh.performOne p .expired
      stop := true
    | a =>
      p ← sh.performOne p a
  return (st, p, stop)

/-- The loop: take an event, step, perform, until the session ends. The
answer is how it ended, with the ports still open. `keepalive` is the
host's interval (`none` for no keepalive). -/
def run (sh : Shared) (role : Role) (keepalive : Option Nat) : Async (Ending × Ports) := do
  let mut st := State.new role keepalive (← (sh.clock.nowMs : BaseIO Nat))
  let mut p : Ports := {}
  repeat
    -- Park: an event wakes it, and so does the close of the queue by
    -- `Session.close`.
    match ← sh.events.recv with
    | none =>
      -- Only `Session.close` closes the queue while the loop runs.
      sh.ownerEnded.set true
      return (.closed, p)
    | some ev =>
      match step st ev with
      | .error e => return (.failed e, p)
      | .ok (st', acts) =>
        let (st'', p', stop) ← sh.performAll st' p acts
        st := st''
        p := p'
        if stop then
          -- A shutdown off the peer's bytes is its normal go-away; the
          -- end of the connection arrives as `.eof`.
          if let .bytes _ := ev then sh.peerGoAway.set true
          return (.shutdown, p)
        -- Back-pressure for the SYN answers (owned contract 5): past the
        -- cap the loop takes no event until the writer has sent enough.
        -- The reader then waits for its credit, and TCP slows the peer.
        repeat
          if (← (sh.controlCount.get : BaseIO Nat)) ≤ controlQueueCap then break
          -- Park: the writer signals each control frame it sends, and
          -- closes the signal when it ends.
          if (← sh.room.recv).isNone then break
        -- The core has charged the read's bytes to their windows, and
        -- the back-pressure wait is over: the reader may read again.
        if let .bytes _ := ev then discard <| sh.credits.trySend ()
  return (.closed, p)

/-- End the session: close every wait it knows, queue the last frame,
and let the writer finish (module doc). -/
def teardown (sh : Shared) (ending : Ending) (p : Ports) : BaseIO Unit := do
  sh.outcome.finish (match ending with | .failed e => .error e | _ => .ok ())
  -- New posts now fail, and the reader stops at its next post, or at
  -- the closed credit.
  sh.events.close
  sh.credits.close
  sh.alarm.close
  -- The write tags stay open: the writer answers each one whose frames
  -- it holds, after it has written them, and closes the table when it
  -- ends. A write that waits on an attempt or on credit wakes now.
  sh.opens.closeAll
  sh.closeAttempts
  for (_, (wp, _)) in p.writers.toList do
    wp.finish .closed
  -- A stream whose peer had not finished reads `closed`, never a bare
  -- EOF (§3.5).
  for (_, inbox) in p.inboxes.toList do
    discard <| inbox.trySend (.error .closed)
    inbox.close
  sh.accepts.close
  let last : Option GoAwayCode := match ending with
    | .closed => some .normal
    | .shutdown => none
    | .failed e => e.reply?
  if let some code := last then sh.queue (.frame (goAwayFrame code).bytes false)
  sh.out.close

/-- The reader task (`Streams.readLoop`; module doc, "The reader's
credit"). The tick goes first, so the core knows when the bytes
arrived. -/
def reader (sh : Shared) : Async Unit :=
  readLoop sh.conn sh.credits sh.outcome.recordFault
    (fun b => do
      if let .error e ← sh.events.send (.tick (← (sh.clock.nowMs : BaseIO Nat))) then
        return .error e
      sh.events.send (.bytes ⟨b⟩))
    (discard <| sh.events.send .eof)

/-- The ticker task (module doc, "The ticks"): it posts a tick at each
deadline the core asked for (`Conc.Alarm`). -/
def ticker (sh : Shared) : Async Unit :=
  sh.alarm.run sh.clock fun now => sh.events.send (.tick now)

/-- The expiry of a write: record the fault, and close the connection,
which wakes the parked write and the reader (PRINCIPLES 3.1). -/
def expireWrite (sh : Shared) : BaseIO Unit := do
  sh.outcome.recordFault (.timeExpired 0 s!"yamux: a write to the peer took longer than {writeDeadlineMs} ms")
  sh.conn.closeQuietly

/-- The writer task. After a failed write the connection is torn down
(§4.7), so the writer stops writing; it still answers the tags, with
`closed`. The reader then sees the end of the connection, and the loop
ends. A failed write records its error (`recordWriteFault`), which reaches
`join` unless the peer's go-away or the owner's close ended the session,
as in go-yamux (`recordWriteFault`). A write that passes
`writeDeadlineMs` records a fault of its own: the peer has stopped
reading.
When the queue ends, the writer closes the write tags, which answers
the writes the loop never took, and then the connection. -/
def writer (sh : Shared) : Async Unit := do
  let mut broken := false
  repeat
    -- Park: the loop's next item wakes it, and so does `teardown`.
    match ← sh.out.recv with
    | none => break
    | some (.frame b control) =>
      if !broken then
        -- Park: the peer's reads wake the write, and so does the close
        -- of the connection at the deadline.
        try
          if let .error _ ← withinDeadline sh.clock writeDeadlineMs sh.expireWrite (sh.conn.write b) then
            broken := true
        catch e =>
          -- A socket error is a fault (§3.5).
          sh.recordWriteFault e
          broken := true
      if control then
        sh.controlCount.update (· - 1)
        discard <| sh.room.trySend ()
    | some (.done tag) =>
      sh.writes.resolve tag (if broken then .error .closed else .ok ())
  sh.writes.closeAll
  sh.room.close
  sh.conn.close

end Shared

end Yamux
