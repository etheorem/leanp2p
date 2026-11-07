import Std.Data.HashMap
import Conc
import Streams
import Libp2p.Protocols.Mock.Core

/-!
# Muxer mock

`Libp2p.Core` (W5.2, PR #37) and the yamux `Muxer` value (W5.4) are not
merged. This mock declares the seam shapes that root ARCHITECTURE §4.9
and the core pair freeze: `Role`, `MuxSession` (`openStream`, `accept`,
`close`, and the completion its owner joins), and `Muxer` with `open :
Role → Connection → ByteArray → ExceptT Error Async MuxSession`. The
value `muxer` runs over any `Connection`, so the req/resp suite runs over
the sim transport (PRINCIPLES 1.4; RULES.md, "Working ahead of the
tree").

## The wire of the mock

One frame shape, and nothing else:

```
<stream id: 4 bytes, big-endian> <kind: 1 byte> <length: 2 bytes, big-endian> <payload>
```

The kind is data (0), close (1), or reset (2). The 2-byte length caps a
frame at 65535 bytes, and the reader takes no more (§5.1). The dialer
numbers its streams odd and the listener even, so the two sides never
pick one id. The first frame of a new id from the peer opens the
stream, and `accept` hands it out. A close ends the peer's read
direction only (§5.3). A reset fails both sides, also after a close.
The end of the session fails every open stream with `.closed`.

The mock enforces no flow control: the inboxes are unbounded, and the
yamux window of W5.4 is what bounds them in production.

## Tasks and parks

One reader task per session, in a `TaskSet` the session owns; `done`
joins it. The reader parks on `Connection.read`, which `close` wakes.
Writers take a one-token channel around each frame write, so two
streams never interleave the bytes of their frames; the token's park
wakes when the writer before it sends the token back.

## Integration

Delete this module. Import `Libp2p.Core` for `Role`, `MuxSession`, and
`Muxer`, and use `Mux.yamux` (W5.4) where the suite takes `muxer`. The
suite needs no other change: it uses the seam fields only.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.Muxer

open Conc Streams
open Libp2p.Protocols.Mock.Core (ProtocolId)

/-- Which end of the connection a session serves. -/
inductive Role where
  /-- The end that dialed. -/
  | initiator
  /-- The end that accepted. -/
  | responder
  deriving DecidableEq, Repr

/-- The uniform session view of the core seam. -/
structure MuxSession where
  /-- Open a stream to the peer. -/
  openStream : ExceptT Core.Error Async Stream
  /-- The next stream the peer opened; `none` after the session closed. -/
  accept : Async (Option Stream)
  /-- Close the session and its connection. -/
  close : IO Unit
  /-- The completion of the session loop, which the owner joins. -/
  done : Async Unit

/-- The muxer seam of the core. -/
structure Muxer where
  /-- The protocol id of the muxer. -/
  id : ProtocolId
  /-- Run a session over a connection. The `ByteArray` holds what the
  negotiation read past its last message. -/
  «open» : Role → Connection → ByteArray → ExceptT Core.Error Async MuxSession

/-! ## Frames -/

/-- The header of a frame: id, kind, length. -/
def headerLen : Nat := 7

/-- The largest payload of one frame. -/
def maxPayload : Nat := 2 ^ 16 - 1

/-- One frame on the wire. -/
def frameB (sid kind : Nat) (payload : ByteArray) : ByteArray :=
  ByteArray.mk #[(sid / 2 ^ 24).toUInt8, (sid / 2 ^ 16).toUInt8, (sid / 2 ^ 8).toUInt8,
    sid.toUInt8, kind.toUInt8, (payload.size / 256).toUInt8, payload.size.toUInt8] ++ payload

/-- The frames of one write: the bytes in pieces of at most `maxPayload`. -/
def dataFramesB (sid : Nat) (bytes : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let pieces := (bytes.size + maxPayload - 1) / maxPayload
  for i in [0:pieces] do
    out := out ++ frameB sid 0 (bytes.extract (i * maxPayload) (i * maxPayload + maxPayload))
  return out

/-- One frame at the front of `b`: the id, the kind, the payload, and the
bytes it took; `none` while the frame is not whole. -/
def readFrame? (b : ByteArray) : Option (Nat × Nat × ByteArray × Nat) :=
  if b.size < headerLen then none
  else
    let byte (i : Nat) : Nat := (b.get! i).toNat
    let sid := ((byte 0 * 256 + byte 1) * 256 + byte 2) * 256 + byte 3
    let len := byte 5 * 256 + byte 6
    if b.size < headerLen + len then none
    else some (sid, byte 4, b.extract headerLen (headerLen + len), headerLen + len)

/-! ## The session -/

/-- The parts of one stream that the reader reaches. -/
structure Entry where
  /-- The chunks the reader delivers. -/
  inbox : Chan (Except Streams.Error ByteArray)
  /-- Set by a reset, so a read after the close of the inbox fails. -/
  rst : OnceRef (Option Streams.Error)

/-- What the streams and the reader of one session share. -/
structure Shared where
  conn : Connection
  /-- The streams by id. Changed only through `update` and `updateGet`. -/
  streams : OnceRef (Std.HashMap Nat Entry)
  /-- The next id this side opens. -/
  next : OnceRef Nat
  /-- The streams the peer opened, for `accept`. -/
  incoming : Chan Stream
  /-- The write token: one frame write at a time. -/
  token : Chan Unit

/-- Write one frame run under the token. A failed write answers `false`. -/
def Shared.send (sh : Shared) (bytes : ByteArray) : Async Bool := do
  -- Park: the writer before this one sends the token back; a session
  -- close closes the token channel and wakes this with `none`.
  let some () ← sh.token.recv | return false
  let ok ← try sh.conn.write bytes; pure true catch _ => pure false
  discard <| sh.token.trySend ()
  return ok

/-- A fresh entry. -/
def newEntry : BaseIO Entry := do
  return ⟨← Chan.newUnbounded, ← OnceRef.new none⟩

/-- The stream of id `sid` over the session. -/
def mkStream (sh : Shared) (sid : Nat) (e : Entry) : BaseIO Stream := do
  let completions ← Completions.new
  Stream.ofPort {
    inbox := e.inbox
    endedBy := e.rst.get
    completions
    postWrite := fun tag bytes => do
      let ok ← sh.send (dataFramesB sid bytes)
      completions.resolve tag (if ok then .ok () else .error .closed)
      return .ok ()
    postConsumed := fun _ => return .ok ()
    postClose := do
      discard <| sh.send (frameB sid 1 ByteArray.empty)
      return .ok ()
    postReset := do
      e.rst.set (some .reset)
      discard <| e.inbox.trySend (.error .reset)
      e.inbox.close
      sh.streams.update (·.erase sid)
      discard <| sh.send (frameB sid 2 ByteArray.empty)
      return .ok () }

/-- Route one frame from the peer. A new id of the peer's parity opens a
stream; a frame for any other unknown id is dropped. -/
def route (sh : Shared) (peerParity : Nat) (sid kind : Nat) (payload : ByteArray) : Async Unit := do
  let entry? ← (sh.streams.get : BaseIO _)
  let e ← match entry?.get? sid with
    | some e => pure (some e)
    | none =>
      if sid % 2 = peerParity ∧ kind ≠ 2 then
        let e ← newEntry
        sh.streams.update (·.insert sid e)
        discard <| sh.incoming.trySend (← mkStream sh sid e)
        pure (some e)
      else pure none
  let some e := e | return
  match kind with
  | 0 => discard <| e.inbox.trySend (.ok payload)
  | 1 => e.inbox.close
  | _ =>
    e.rst.set (some .reset)
    discard <| e.inbox.trySend (.error .reset)
    e.inbox.close
    sh.streams.update (·.erase sid)

/-- The reader loop. `partial`: a peer may send frames forever; the
session's close ends the connection read with `none`, which ends the
loop. At the end every inbox and `incoming` close, so each parked read
and accept wakes. -/
partial def readLoop (sh : Shared) (peerParity : Nat) (buf : ByteArray) : Async Unit := do
  match readFrame? buf with
  | some (sid, kind, payload, k) =>
    route sh peerParity sid kind payload
    readLoop sh peerParity (buf.extract k buf.size)
  | none =>
    -- Park: the peer's bytes wake it, and so does `close` of the connection.
    match ← sh.conn.read with
    | some b => readLoop sh peerParity (buf ++ b)
    | none =>
      -- The session ended under the open streams, so a read after this
      -- answers `.closed`, the failure §5.2 keeps apart from an end.
      for (_, e) in (← (sh.streams.get : BaseIO _)).toList do
        e.rst.update fun r => r <|> some .closed
        e.inbox.close
      sh.incoming.close
      sh.token.close

/-- Run a mock session over `conn`. -/
def openSession (role : Role) (conn : Connection) (leftover : ByteArray) :
    ExceptT Core.Error Async MuxSession := do
  let token : Chan Unit ← Chan.new 1
  discard <| token.trySend ()
  let sh : Shared := {
    conn
    streams := ← OnceRef.new {}
    next := ← OnceRef.new (if role = .initiator then 1 else 2)
    incoming := ← Chan.newUnbounded
    token }
  let owner ← TaskSet.new
  let peerParity := if role = .initiator then 0 else 1
  owner.spawn (readLoop sh peerParity leftover)
  return {
    openStream := do
      let sid ← (sh.next.updateGet fun n => (n, n + 2) : BaseIO Nat)
      let e ← newEntry
      sh.streams.update (·.insert sid e)
      mkStream sh sid e
    accept := sh.incoming.recv
    close := sh.conn.close
    done := owner.joinAll }

/-- The mock muxer value. -/
def muxer : Muxer := ⟨⟨"/leanp2p-mock-mux/1.0.0"⟩, openSession⟩

end Libp2p.Protocols.Mock.Muxer
