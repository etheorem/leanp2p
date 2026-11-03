import Std
import Conc
import Streams

/-!
# Core seam mock

`Libp2p.Core` (issue #15, PR #37 draft) is not merged. This mock
declares the frozen seam shapes from
`packages/libp2p/core/docs/ARCHITECTURE.md`: the `ProtocolId` of
sub-unit 1a, and the coarse `Error` and the `StreamHandler` of
sub-unit 1b. The real core package replaces this module at
integration.
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
served stream reaches. -/
structure StreamHandler where
  id : ProtocolId
  handle : Streams.Stream → ExceptT Error Conc.Async Unit

/-- One map from a stream answer to the coarse error, shared by every
handler of this package. `closed` stays closed, `reset` is a protocol
fault, and `timeout` stays timeout. -/
def mapStreamError : Streams.Error → Error
  | .closed => .closed "the stream closed"
  | .reset => .protocol "the peer reset the stream"
  | .timeout => .timeout "the stream deadline expired"

end Libp2p.Protocols.Mock.Core
