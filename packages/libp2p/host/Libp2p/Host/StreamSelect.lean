import Streams
import Bytes
import Libp2p.Core
import Libp2p.Negotiate

/-!
# Protocol selection on a muxed stream

Every stream the muxer opens starts with its own multistream-select
1.0.0 exchange (the connection spec, "Opening new streams over a
multiplexed connection"): the initiator proposes the protocol ids in
order, and the responder answers with the first one in its handler
table. This module runs that exchange on a `Streams.Stream`.

The negotiate package drives the same pure core over a
`Streams.Connection` (`Negotiate.negotiate`), for the security and muxer
stages of the upgrade. A muxed stream is a different seam: it reads and
writes through `Except` answers, and it carries a read-back buffer for
the leftover. The host owns this shell, and it reuses the core
unchanged: `initiatorStart`, `responderStart`, `drive`, and
`mapNegotiateError` all come from `Libp2p.Negotiate`.

The bytes that follow the selection on the same read belong to the
protocol. `Stream.prependBytes` hands them on to the handler
(ARCHITECTURE §5.6).

The read parks for as long as the peer stays silent, so no measure
bounds the loop (root §3.3). The `repeat` form keeps the definition free
of a `partial` marker, as in `Negotiate.negotiate`.
-/

set_option autoImplicit false

namespace Libp2p.Host

open Libp2p.Negotiate (initiatorStart responderStart drive mapNegotiateError)

/-- Write each frame payload of the core to the stream, in order. A
failed write is the `closed` arm: the stream is gone. -/
private def sendWrites (stream : Streams.Stream) (ws : List (List Nat)) :
    ExceptT Libp2p.Core.Error Conc.Async Unit := do
  for w in ws do
    if let .error e ← stream.write (Bytes.ofNatList w) then
      throw (.closed s!"stream negotiation write failed: {repr e}")

/-- Negotiate a protocol on a muxed stream. The answer is the selected
id and the stream with the bytes after the selection put back in front
of its reads. -/
def negotiateStream (role : Libp2p.Core.Role) (stream : Streams.Stream)
    (ids : List Libp2p.Core.ProtocolId) :
    ExceptT Libp2p.Core.Error Conc.Async (Libp2p.Core.ProtocolId × Streams.Stream) := do
  let start := match role with
    | .initiator => initiatorStart ids
    | .responder => responderStart ids
  let (initial, first) ← match start with
    | .error e => throw (mapNegotiateError e)
    | .ok pair => pure pair
  sendWrites stream first
  let mut state := initial
  let mut input : List Nat := []
  repeat
    match drive 1 state input with
    | .error e => throw (mapNegotiateError e)
    | .ok (.selected p _ rest writes) =>
        sendWrites stream writes
        return (p, ← Streams.Stream.prependBytes stream (Bytes.ofNatList rest))
    | .ok (.running s _ rest writes) =>
        sendWrites stream writes
        state := s
        input := rest
    | .ok (.waiting s _ rest writes) =>
        sendWrites stream writes
        state := s
        match ← stream.read with
        | .error e => throw (.closed s!"stream negotiation read failed: {repr e}")
        | .ok none => throw (.closed "stream ended during negotiation")
        | .ok (some bytes) => input := rest ++ Bytes.toNatList bytes
  -- Every arm above returns or loops, so the `repeat` never falls
  -- through. The tail gives the `do` block its result type.
  throw (.closed "stream negotiation ended without a selection")

end Libp2p.Host
