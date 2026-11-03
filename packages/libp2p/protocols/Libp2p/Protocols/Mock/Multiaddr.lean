import Std

/-!
# Multiaddr mock

`Multiformats` (issue #8, PR #36, unmerged) owns the real
`Multiaddr.ofByteArray?`. This mock declares the minimal validity
predicate that the identify validate needs. The real check replaces
it at integration.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.Multiaddr

/-- Executable stand-in: the empty address is invalid, every other
buffer is valid. -/
opaque validBytes (bs : List Nat) : Bool :=
  !bs.isEmpty

end Libp2p.Protocols.Mock.Multiaddr
