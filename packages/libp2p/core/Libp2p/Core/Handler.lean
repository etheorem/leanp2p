import Conc
import Libp2p.Core.Error
import Libp2p.Core.ProtocolId
import Libp2p.Core.Mock.Streams

/-!
# Stream handlers

The host registers handlers by `ProtocolId` (ARCHITECTURE §3.10).
Before invoking a handler, it restores negotiation leftovers with
`Stream.prependBytes`, so the callback reads from the first protocol
byte (§4.7).
-/

set_option autoImplicit false

namespace Libp2p.Core

open Libp2p.Core.Mock

/-- A callback serving streams for one negotiated protocol. -/
structure StreamHandler where
  /-- The protocol id used for registration and negotiation. -/
  id : ProtocolId
  /-- Serve one stream. The handler owns the stream: it closes or
  resets the stream before it answers. A protocol failure is an
  `Error`. The host decides its effect on the connection. -/
  handle : Streams.Stream → ExceptT Error Conc.Async Unit

end Libp2p.Core
