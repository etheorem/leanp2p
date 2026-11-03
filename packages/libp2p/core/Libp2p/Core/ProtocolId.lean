/-!
# Protocol identifiers

Protocol identifiers are compared exactly, without normalization.
The multistream codec enforces wire-format restrictions. Known ids
live with their protocol implementations (ARCHITECTURE §3.4).
-/

set_option autoImplicit false

namespace Libp2p.Core

/-- An application-defined protocol name used by multistream-select. -/
structure ProtocolId where
  /-- The id as the peer sends it, without the multistream newline. -/
  toString : String
  deriving DecidableEq, Hashable, Ord, Repr

namespace ProtocolId

/-- Print the protocol name as it appears on the wire. -/
instance : ToString ProtocolId := ⟨ProtocolId.toString⟩

/-- Equality of protocol ids is exact equality of their strings. -/
theorem eq_iff_toString_eq (a b : ProtocolId) : a = b ↔ a.toString = b.toString := by
  cases a
  cases b
  simp

end ProtocolId

end Libp2p.Core
