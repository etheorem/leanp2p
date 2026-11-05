/-!
# Mock: the surface of `libp2p/identity` that the host uses

W5.1 (`libp2p/identity`) has not merged, so the host builds against a
mock of its frozen surface (RULES.md, "Working ahead of the tree"; the
identity ARCHITECTURE, "Public surface"). The mock imports nothing from
the real package, and it states no axiom.

* `PeerId` is a copy of the shape the host reads: the binary form
  (`toBytes`, the multihash bytes of the peer-ids spec) and the text
  form it prints. A test builds one directly.
* `PubKey` and `PrivKey` are copies that hold their bytes.
* The derivations are `opaque`, and each fails with the name of the
  package, so no run derives an identity from this mock.

At the integration, the host imports `Libp2p.Identity`, drops
`open Libp2p.Host.Mock`, and the module goes.
-/

set_option autoImplicit false

namespace Libp2p.Host.Mock.Identity

/-- Why a key or a peer id failed to derive or to parse. -/
inductive Error where
  /-- The identity package is not integrated. -/
  | unavailable (what : String)
  deriving DecidableEq, Repr

/-- A peer id. -/
structure PeerId where
  /-- The binary form: the multihash bytes (the peer-ids spec). -/
  bytes : List Nat
  /-- The text form the id prints. -/
  text : String
  deriving DecidableEq, Hashable, Repr

namespace PeerId

/-- The binary form, the bytes a `/p2p` component carries. -/
def toBytes (p : PeerId) : ByteArray := ⟨(p.bytes.map UInt8.ofNat).toArray⟩

instance : ToString PeerId := ⟨PeerId.text⟩

end PeerId

/-- A public key. -/
structure PubKey where
  /-- The marshaled key. -/
  raw : ByteArray

/-- A private key. -/
structure PrivKey where
  /-- The marshaled key. -/
  raw : ByteArray

/-- The public half of a private key. -/
opaque PrivKey.toPublic (_k : PrivKey) : Except Error PubKey :=
  .error (.unavailable "libp2p/identity (W5.1): key derivation")

/-- The peer id of a public key. -/
opaque PeerId.ofPubKey (_k : PubKey) : Except Error PeerId :=
  .error (.unavailable "libp2p/identity (W5.1): peer id derivation")

/-- The peer id of its binary form, the value of a `/p2p` component. -/
opaque PeerId.ofBytes? (_b : ByteArray) : Except Error PeerId :=
  .error (.unavailable "libp2p/identity (W5.1): peer id parse")

end Libp2p.Host.Mock.Identity
