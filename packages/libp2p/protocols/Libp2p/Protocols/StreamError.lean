import Streams.Error
import Libp2p.Core.Error

set_option autoImplicit false

namespace Libp2p.Protocols

/-- Map a stream failure to the core error at a protocol boundary. -/
def mapStreamError : Streams.Error → Libp2p.Core.Error
  | .closed => .closed "the stream closed"
  | .reset => .protocol "the peer reset the stream"
  | .timeout => .timeout "the stream deadline expired"

end Libp2p.Protocols
