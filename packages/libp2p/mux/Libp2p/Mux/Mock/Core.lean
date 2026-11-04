/-!
# Mock: the `ProtocolId` surface of `libp2p/core`

W5.2 (`libp2p/core`) is not yet merged, so this package builds against
a temporary copy of the documented `ProtocolId` surface (RULES.md,
"Working ahead of the tree"; the core pair, public surface). The copy
is `structure ProtocolId where toString : String`. It derives
`DecidableEq` and `Hashable` from that surface, and `Repr` from the
standard identifier classes (ARCHITECTURE §3.2, §3.4).

The module holds no protocol logic. It adds no trusted declarations.
When W5.2 lands, delete this module. `Constants.lean` then imports
`Libp2p.Core` in its place.
-/

set_option autoImplicit false

namespace Libp2p.Mux.Mock.Core

/-- A protocol id: an open wrapped string (ARCHITECTURE §3.4). Peers
define ids, so the set stays open. -/
structure ProtocolId where
  toString : String
  deriving DecidableEq, Repr, Hashable

end Libp2p.Mux.Mock.Core
