import Std
import Conc
import Streams
import Libp2p.Identity

/-!
# Core seam mock

`Libp2p.Core` (issue #15, PR #37) is not merged. This mock declares
the frozen seam shapes from `packages/libp2p/core/docs/ARCHITECTURE.md`:
`ProtocolId`, the coarse `Error`, and `StreamHandler`. The real core
package replaces this module at integration.
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

/-- The handler seam: the id it registers under, and the callback a
served stream reaches. The host looks a handler up by the protocol id
alone, and it knows the peer at the call site, so the seam carries the
peer. A gossipsub handler needs that id, because the core scores and
filters by the sender of each RPC. -/
structure StreamHandler where
  /-- The id the handler serves. -/
  id : ProtocolId
  /-- The offered stream and the peer that opened it. -/
  handle : Libp2p.Identity.PeerId → Streams.Stream → ExceptT Error Conc.Async Unit

/-- One map from a stream error to the coarse error, shared by every
handler of this package. `closed` stays closed, `reset` is a protocol
fault, and `timeout` stays timeout. -/
def mapStreamError : Streams.Error → Error
  | .closed => .closed "the stream closed"
  | .reset => .protocol "the peer reset the stream"
  | .timeout => .timeout "the stream deadline expired"

end Libp2p.Protocols.Mock.Core
