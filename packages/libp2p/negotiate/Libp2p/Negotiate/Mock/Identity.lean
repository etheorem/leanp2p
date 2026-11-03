import Std

/-!
# Identity mocks for unit 1b

`PeerId` lives in `libp2p/identity` (#11, not merged yet). The real
type is a proof-carrying newtype over a validated multihash
(identity ARCHITECTURE, "Public surface"). The upgrader compares
`PeerId` values only, so this mock keeps the recorded one-field form
and the derived classes (plan.md, "Mock surface"). The import swaps
to `Libp2p.Identity` when the identity package lands.
-/

set_option autoImplicit false

namespace Libp2p.Negotiate.Mock.Identity

/-- The one-field mock of the validated multihash. The upgrader
compares values only. -/
structure PeerId where
  toString : String
  deriving DecidableEq, Repr, Hashable

end Libp2p.Negotiate.Mock.Identity
