import Streams
import Libp2p.Core.Error

/-!
# The stream error at the handler seam

A handler of this package reads and writes one negotiated `Stream`, and
a failed read or write answers a `Streams.Error`. The handler seam of
`libp2p/core` fails with the coarse `Core.Error` (ARCHITECTURE §3.5),
so each handler maps the stream error once, through this function.
Identify, ping, and req/resp share it.
-/

set_option autoImplicit false

namespace Libp2p.Protocols

/-- The one map from a stream error to the coarse core error. `closed`
stays closed, `reset` is a protocol fault, and `timeout` stays
timeout. -/
def mapStreamError : Streams.Error → Libp2p.Core.Error
  | .closed => .closed "the stream closed"
  | .reset => .protocol "the peer reset the stream"
  | .timeout => .timeout "the stream deadline expired"

end Libp2p.Protocols
