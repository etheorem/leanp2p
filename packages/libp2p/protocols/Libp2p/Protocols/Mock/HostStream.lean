import Conc
import Streams
import Libp2p.Core.Handler
import Libp2p.Core.Mux
import Libp2p.Protocols.StreamError

/-!
# Host stream mock

`Libp2p.Host` (W5.6) merged, but it still runs its upgrade through a
mock of `libp2p/negotiate` (issue #70), so no host opens a session yet.
The protocols docs have the req/resp client open its stream through
the host, with `newStream`, and serve through `setHandler` over the
registry of §3.10; go-libp2p's outbound call is `NewStream`
(`vendor/go-libp2p/p2p/host/basic/basic_host.go`, line 441). This
mock fixes minimal signatures for both sides over one muxer session of
the real `MuxSession` seam (RULES.md, "Working ahead of the tree").

## What it leaves out

* Dialing: the mock holds one session, so `newStream` needs no peer.
* Negotiation (W5.5): the opener writes the first id it asks for, with a
  one-byte length (an id of at most 255 bytes), and the listener looks
  the id up in its registry. An id it does not serve resets the stream.
  The bytes the listener read past the id go in front of the stream
  with `Stream.prependBytes` (§4.7), as the negotiation hands them on.
* Failure reporting: a handler's failure goes to `failures`, the place
  the host's `onFailure` will take.

## Tasks and parks

`serve` accepts in a loop and runs each stream in a task of a set it
owns, then joins the set when the session ends. The accept parks on the
session, which `close` ends. `close` closes the session, and `join`
waits for the serve loop and the session loop.

## Integration

Delete this module. Use the host's `newStream` for the peer, bound to
the peer id, in place of `Host.newStream`, and the host's `setHandler`
in place of `Host.setHandler`.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.HostStream

open Conc Streams
open Libp2p.Core (ProtocolId StreamContext StreamHandler MuxSession)

/-- One end of a peer connection, with its handler registry. -/
structure Host where
  /-- The mock session to the peer. -/
  session : MuxSession
  /-- The context every served stream of the session gets: the peer and
  its address, which the real host takes from the upgrade. -/
  ctx : StreamContext
  /-- The registry, by protocol id; changed only through `update`. -/
  handlers : OnceRef (List StreamHandler)
  /-- The handler failures, newest first. -/
  failures : OnceRef (List Libp2p.Core.Error)
  /-- The tasks of the served streams and the serve loop. -/
  owner : TaskSet

/-- A host over a session to the peer that `ctx` names. -/
def Host.new (session : MuxSession) (ctx : StreamContext) : BaseIO Host := do
  return ⟨session, ctx, ← OnceRef.new [], ← OnceRef.new [], ← TaskSet.new⟩

/-- Store one handler under its id; a second store replaces the first. -/
def Host.setHandler (h : Host) (sh : StreamHandler) : BaseIO Unit :=
  h.handlers.update fun hs => sh :: hs.filter (·.id != sh.id)

/-- The header the opener writes: the id with a one-byte length. -/
def idHeader (id : ProtocolId) : Option ByteArray :=
  let b := id.toString.toUTF8
  if b.size < 256 then some (ByteArray.mk #[b.size.toUInt8] ++ b) else none

/-- Open a stream to the peer for the first id of `protocols`. -/
def Host.newStream (h : Host) (protocols : List ProtocolId) :
    Async (Except Libp2p.Core.Error (ProtocolId × Stream)) := do
  let some id := protocols.head? | return .error (.protocol "newStream: no protocol id")
  let some header := idHeader id | return .error (.protocol "newStream: an id over 255 bytes")
  match ← (h.session.openStream id).run with
  | .error e => return .error e
  | .ok s =>
    match ← s.write header with
    | .error e => s.reset; return .error (mapStreamError e)
    | .ok () => return .ok (id, s)

/-- Read the id header from `s`: the id and the bytes after it. `none`
when the stream ends or fails first. The read parks on the stream, which
the session close or a reset wakes; the loop is `partial` for the same
reason as every stream read loop. -/
partial def readHeader (s : Stream) (buf : ByteArray) : Async (Option (String × ByteArray)) := do
  if h : 0 < buf.size then
    let len := (buf.get 0 h).toNat
    if 1 + len ≤ buf.size then
      return (String.fromUTF8? (buf.extract 1 (1 + len))).map fun id =>
        (id, buf.extract (1 + len) buf.size)
  match ← s.read with
  | .ok (some b) => readHeader s (buf ++ b)
  | _ => return none

/-- Serve one inbound stream through the registry. -/
def serveStream (h : Host) (s : Stream) : Async Unit := do
  let some (id, rest) ← readHeader s ByteArray.empty | s.reset
  let hs ← (h.handlers.get : BaseIO _)
  match hs.find? (·.id.toString == id) with
  | none => s.reset
  | some sh =>
    let s ← s.prependBytes rest
    match ← (sh.handle h.ctx s).run with
    | .ok () => pure ()
    | .error e =>
      h.failures.update (e :: ·)
      s.reset

/-- The serve loop: accept until the session ends, one task per stream.
`partial`: the peer may open streams forever; the session close ends the
accept with `none`. -/
partial def serveLoop (h : Host) (streams : TaskSet) : Async Unit := do
  -- Park: a new stream of the peer wakes it, and so does the close.
  match ← h.session.accept with
  | none => streams.joinAll
  | some s =>
    streams.spawn (serveStream h s)
    serveLoop h streams

/-- Start serving inbound streams. -/
def Host.serve (h : Host) : BaseIO Unit := do
  let streams ← TaskSet.new
  h.owner.spawn (serveLoop h streams)

/-- Close the session. -/
def Host.close (h : Host) : IO Unit := h.session.close

/-- Wait for the serve loop, its streams, and the session loop. The
session of `Mock.Muxer.muxer` always joins with `.ok`, so the answer
goes unread. -/
def Host.join (h : Host) : Async Unit := do
  h.owner.joinAll
  discard h.session.join.run

end Libp2p.Protocols.Mock.HostStream
