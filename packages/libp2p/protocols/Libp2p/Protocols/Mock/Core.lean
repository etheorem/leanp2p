import Std

/-!
# ProtocolId mock

`Libp2p.Core` (issue #15, PR #37 draft) is not merged. This mock
declares the frozen `ProtocolId` shape from
`packages/libp2p/core/docs/ARCHITECTURE.md`. The real core package
replaces this module at integration.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.Core

/-- A peer-defined protocol id, an open set of strings. The code
compares `ProtocolId` values only. -/
structure ProtocolId where
  toString : String
  deriving DecidableEq, Hashable

end Libp2p.Protocols.Mock.Core
