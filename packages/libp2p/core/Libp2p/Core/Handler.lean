import Conc
import Streams
import Libp2p.Core.ProtocolId
import Libp2p.Core.Error

/-!
# The stream handler seam

When the peer opens a stream, it proposes a protocol id with
multistream-select, and the host answers with the handler registered
under that id (the connections spec, "Protocol Negotiation"). The host
keys its registry by the id, `Std.HashMap ProtocolId StreamHandler`
(ARCHITECTURE §3.10), and hands the negotiated stream to the callback.
The stream already carries the bytes the stream negotiation read past
its last message (`Stream.prependBytes`, §4.7).

A protocol package builds its handler value with the id constant of
its own module (§3.4). A handler failure closes the stream and leaves
the session open; the host makes that call (the host pair, public
surface).
-/

set_option autoImplicit false

namespace Libp2p.Core

open Conc Streams

/-- The handler of one protocol: the id the host registers it under,
and the callback that serves a negotiated stream. -/
structure StreamHandler where
  /-- The protocol id the host matches proposals against. -/
  id : ProtocolId
  /-- Serve one stream. `.error` reports a protocol failure on this
  stream to the host. -/
  handle : Stream → ExceptT Error Async Unit

end Libp2p.Core
