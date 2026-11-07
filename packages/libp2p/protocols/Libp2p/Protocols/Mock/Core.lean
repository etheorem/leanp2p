import Std
import Conc
import Streams
import Libp2p.Identity

/-!
# Core seam mock

`Libp2p.Core` (issue #15, PR #64) is not merged. This mock declares
the frozen seam shapes from `packages/libp2p/core/docs/ARCHITECTURE.md`:
`ProtocolId`, the coarse `Error`, `StreamContext`, and `StreamHandler`.
The real core package replaces this module at integration.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.Core

/-- A peer-defined protocol id, an open set of strings. The code
compares `ProtocolId` values only. -/
structure ProtocolId where
  toString : String
  deriving DecidableEq, Hashable

/-- The coarse error of the core seam, with the rendered inner error. -/
inductive Error where
  | protocol (rendered : String)
  | authentication (rendered : String)
  | timeout (rendered : String)
  | closed (rendered : String)
  deriving DecidableEq, BEq, Repr

/-- What the host knows about the connection under a served stream:
the proved peer id and the peer's transport address. -/
structure StreamContext where
  remotePeer : Libp2p.Identity.PeerId
  remoteAddr : Multiformats.Multiaddr

/-- The handler seam: the id it registers under, and the callback a
served stream reaches. -/
structure StreamHandler where
  id : ProtocolId
  handle : StreamContext → Streams.Stream → ExceptT Error Conc.Async Unit

/-- One map from a stream error to the coarse error, shared by every
handler of this package. `closed` stays closed, `reset` is a protocol
fault, and `timeout` stays timeout. -/
def mapStreamError : Streams.Error → Error
  | .closed => .closed "the stream closed"
  | .reset => .protocol "the peer reset the stream"
  | .timeout => .timeout "the stream deadline expired"

end Libp2p.Protocols.Mock.Core
