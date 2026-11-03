import Std

/-!
# Identity mock

`Libp2p.Identity` (issue #11) is not merged. This mock declares the
frozen key and peer id shapes from
`packages/libp2p/identity/docs/ARCHITECTURE.md`. The real identity
package replaces this module at integration.

`PubKey` drops the validity proof field of the real shape. The
stand-in bodies are executable, so the suite can drive both outcomes
of `unmarshalPubKey?`. The theorems of `Identify` stay true for any
replacement, because they are conditional on these opaque results.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Mock.Identity

/-- The closed set of key types: rsa (0), ed25519 (1), secp256k1 (2),
ecdsa (3). -/
inductive KeyType where
  | rsa | ed25519 | secp256k1 | ecdsa
  deriving DecidableEq, BEq, Repr

/-- A public key: its type and its data bytes. -/
structure PubKey where
  keyType : KeyType
  data : List Nat
  deriving DecidableEq, Repr

/-- A peer id: the derived bytes and the text form. -/
structure PeerId where
  bytes : List Nat
  text : String
  deriving DecidableEq, BEq, Repr

/-- Executable stand-in: a nonempty buffer parses as an ed25519 key,
an empty buffer does not parse. -/
opaque unmarshalPubKey? (bs : List Nat) : Option PubKey :=
  if bs.isEmpty then none else some ⟨.ed25519, bs⟩

/-- Executable stand-in: the derived id carries the key bytes. -/
opaque peerIdOfPubKey (k : PubKey) : PeerId :=
  ⟨k.data, ""⟩

/-- Executable stand-in: the raw key data. The mock `unmarshalPubKey?`
parses any nonempty buffer as `⟨.ed25519, buffer⟩`, and `peerIdOfPubKey`
reads only the buffer, so the round trip holds for a nonempty ed25519
stand-in. The real identity package writes the serialized PublicKey
protobuf (peer-ids spec); that body replaces this one at integration. -/
opaque marshalPubKey (k : PubKey) : List Nat :=
  k.data

end Libp2p.Protocols.Mock.Identity
