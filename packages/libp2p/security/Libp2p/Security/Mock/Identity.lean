import Bytes
import Proto
import Multiformats
import Crypto

/-!
# Mock: the surface of `libp2p/identity` that Noise uses

W5.1 (`libp2p/identity`, etheorem/leanp2p#11) has not merged, so this
package builds against a mock of its frozen surface (RULES.md, "Working
ahead of the tree"; the identity ARCHITECTURE, "Public surface"). The
mock imports nothing from the real package, and it states no axiom.

The names and the shapes follow the identity ARCHITECTURE: `KeyType`,
`PubKey` with `unmarshal?`, `marshal`, `data`, and `verify`, `PrivKey`
with `ofData?`, `toPublic`, and `sign`, `PeerId` with `ofPubKey` and its
text form, and `Identity.Error`, a copy of the real error inductive.

**Why the opaques have values.** The Noise suites sign and verify real
handshake payloads, and the go transcript checks the peer ids that
go-libp2p printed, so the mock computes. It covers Ed25519 alone, the
key type of every Noise suite and of go-libp2p's default identity:

* the `Keys` protobuf of the peer-ids spec, field 1 the varint `Type`
  and field 2 the `Data` bytes, with an Ed25519 `Data` of 32 bytes;
* the peer id: the marshaled key is 36 bytes, at most 42, so it
  inlines as an identity multihash, and its text form is base58btc;
* signing and verification through the Ed25519 entries of the facade.

Every other key type fails with `keyData`. The kernel sees no
definition, so no proof can unfold one. At the integration, the
package imports `Libp2p.Identity`, drops `open Libp2p.Security.Mock`,
and the module goes.
-/

set_option autoImplicit false

namespace Libp2p.Security.Mock.Identity

open Bytes

/-- The key types of the peer-ids spec. -/
inductive KeyType where
  | rsa
  | ed25519
  | secp256k1
  | ecdsa
  deriving DecidableEq, Repr

/-- The protobuf code of a key type (the peer-ids spec, `KeyType`). -/
def KeyType.toCode : KeyType → Nat
  | .rsa => 0
  | .ed25519 => 1
  | .secp256k1 => 2
  | .ecdsa => 3

/-- A failure of the identity package: a copy of the real arms. -/
inductive Error where
  | message (e : Pb.Error)
  | missingField (field : Nat)
  | badKeyType (code : Nat)
  | keyData (t : KeyType) (size : Nat)
  | publicMismatch
  | crypto (e : Crypto.CryptoError)
  | peerIdCodec (e : Multiformats.Error)
  | notPeerShape
  deriving Repr, BEq

/-- A public key: its type and its `Data` bytes. -/
structure PubKey where
  keyType : KeyType
  data : ByteArray

instance : Repr PubKey where
  reprPrec k _ := s!"PubKey {repr k.keyType} {toHex k.data}"

/-- A private key: its type and the Ed25519 seed. -/
structure PrivKey where
  keyType : KeyType
  seed : Crypto.Key32

/-- A peer id: the bytes of its multihash. -/
structure PeerId where
  bytes : ByteArray

instance : BEq PeerId := ⟨fun a b => a.bytes == b.bytes⟩

instance : Repr PeerId where
  reprPrec p _ := s!"PeerId {toHex p.bytes}"

namespace Impl

/-- The `Keys` protobuf of an Ed25519 key: field 1 (`Type`, varint 1),
then field 2 (`Data`, 32 bytes). -/
def ed25519Header : ByteArray := ⟨#[0x08, 0x01, 0x12, 0x20]⟩

def marshal (k : PubKey) : ByteArray := ed25519Header ++ k.data

def unmarshal? (b : ByteArray) : Except Error PubKey :=
  if b.size == 36 && b.extract 0 4 == ed25519Header then .ok ⟨.ed25519, b.extract 4 36⟩
  else .error (.keyData .ed25519 b.size)

def verify (k : PubKey) (msg sig : ByteArray) : Bool :=
  match k.keyType with
  | .ed25519 => Crypto.ed25519Verify k.data msg sig
  | _ => false

def privOfData? (t : KeyType) (d : ByteArray) : Except Error PrivKey :=
  match t, Crypto.Key32.ofByteArray? d with
  | .ed25519, some seed => .ok ⟨.ed25519, seed⟩
  | _, _ => .error (.keyData t d.size)

def toPublic (k : PrivKey) : Except Error PubKey := do
  let pub ← (Crypto.ed25519PublicKey k.seed).mapError .crypto
  return ⟨.ed25519, pub.bytes⟩

def sign (k : PrivKey) (msg : ByteArray) : ExceptT Error IO ByteArray :=
  ExceptT.mk (pure ((Crypto.ed25519Sign k.seed msg).mapError .crypto))

/-- The identity multihash of the marshaled key: code `0x00`, then the
length, then the bytes. -/
def ofPubKey (k : PubKey) : Except Error PeerId :=
  let m := marshal k
  .ok ⟨ByteArray.mk #[0x00, m.size.toUInt8] ++ m⟩

end Impl

/-- The strict unmarshal of a marshaled `PublicKey`. -/
opaque PubKey.unmarshal? : ByteArray → Except Error PubKey := Impl.unmarshal?

/-- The deterministic marshaling of a public key. -/
opaque PubKey.marshal : PubKey → ByteArray := Impl.marshal

/-- Verify a signature of `msg` under the key. -/
opaque PubKey.verify : PubKey → ByteArray → ByteArray → Bool := Impl.verify

/-- The private key of a key type and its `Data` bytes. -/
opaque PrivKey.ofData? : KeyType → ByteArray → Except Error PrivKey := Impl.privOfData?

/-- The public key of a private key. -/
opaque PrivKey.toPublic : PrivKey → Except Error PubKey := Impl.toPublic

/-- Sign `msg` with the key. -/
opaque PrivKey.sign : PrivKey → ByteArray → ExceptT Error IO ByteArray := Impl.sign

/-- The peer id of a public key. -/
opaque PeerId.ofPubKey : PubKey → Except Error PeerId := Impl.ofPubKey

/-- The legacy base58btc text form of a peer id. -/
opaque PeerId.toString : PeerId → String := fun p => Multiformats.Base58.encode p.bytes

instance : ToString PeerId := ⟨PeerId.toString⟩

end Libp2p.Security.Mock.Identity
