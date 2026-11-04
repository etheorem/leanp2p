import Bytes

/-!
# The mock of the W5.1 key and peer-id surface

Unit W5.1 (`libp2p/identity`, the keys and `PeerId`,
etheorem/leanp2p#11) has not merged. RULES.md, "Working ahead of the
tree", tells a unit to build against a mock of the frozen interface of
a dependency that has not merged. The package ARCHITECTURE, "Public
surface", freezes the shape that the ENR mapping needs:

* `KeyType`, the closed set of four, with `secp256k1` at code 2.
* `PubKey`, a key type and its `Data` bytes, built by the strict
  unmarshal: a secp256k1 `Data` is the 33-byte SEC1 compressed point.
* `PeerId`, the validated multihash over the marshaled `Keys`
  protobuf. A marshaled key of at most 42 bytes inlines as an identity
  multihash. Its legacy text form is base58btc.

The docs fix no function names for the strict unmarshal and the
derivation, so the mock names them `PubKey.ofData?` and
`PeerId.ofPubKey`. The integration renames the two calls in
`Enr/Mapping.lean` to the names W5.1 lands.

**Why the opaques have values.** The mapping test derives the peer id
of the EIP-778 key and compares it with a fixed string, so the mock
computes it: the `Keys` protobuf (field 1 varint `Type`, field 2 bytes
`Data`, peer-ids spec), the identity multihash, and base58btc. The
kernel sees no definition, so no proof can unfold one.
-/

set_option autoImplicit false

namespace Libp2p.Identity.Mock.Keys

/-- The key types of the peer-ids spec. -/
inductive KeyType where
  | rsa
  | ed25519
  | secp256k1
  | ecdsa
  deriving DecidableEq, Repr

/-- The protobuf code of a key type. -/
def KeyType.toCode : KeyType → Nat
  | .rsa => 0
  | .ed25519 => 1
  | .secp256k1 => 2
  | .ecdsa => 3

/-- A public key: its type and its `Data` bytes. -/
structure PubKey where
  keyType : KeyType
  data : ByteArray

/-- A peer id: the bytes of its multihash. -/
structure PeerId where
  bytes : ByteArray

namespace Impl

def base58Alphabet : String := "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

/-- base58btc: each leading zero byte becomes one `1`. -/
def base58 (b : ByteArray) : String := Id.run do
  let zeros := (b.toList.takeWhile (· == 0)).length
  let mut v := b.foldl (fun acc x => acc * 256 + x.toNat) 0
  let mut digits : List Char := []
  while v > 0 do
    digits := (base58Alphabet.toList.getD (v % 58) '1') :: digits
    v := v / 58
  return String.ofList (List.replicate zeros '1' ++ digits)

/-- The strict per-type `Data` check that the mapping needs: a
secp256k1 key is 33 bytes. -/
def ofData? (t : KeyType) (data : ByteArray) : Option PubKey :=
  match t with
  | .secp256k1 => if data.size = 33 then some ⟨t, data⟩ else none
  | _ => some ⟨t, data⟩

/-- The `Keys` protobuf of a key with a `Data` under 128 bytes, inlined
as an identity multihash. The mock has no sha2-256 branch for a key
over 42 bytes: the mapping passes only the 33-byte secp256k1 key, whose
protobuf is 37 bytes. W5.1 lands the threshold. -/
def ofPubKey (k : PubKey) : PeerId :=
  let pb := ByteArray.mk #[0x08, k.keyType.toCode.toUInt8, 0x12, k.data.size.toUInt8] ++ k.data
  ⟨ByteArray.mk #[0x00, pb.size.toUInt8] ++ pb⟩

end Impl

/-- The strict unmarshal of a key's `Data`, or `none` when the length
does not fit the type. -/
opaque PubKey.ofData? : KeyType → ByteArray → Option PubKey := Impl.ofData?

/-- The peer id of a public key. -/
opaque PeerId.ofPubKey : PubKey → PeerId := Impl.ofPubKey

/-- The legacy base58btc text form. -/
opaque PeerId.toBase58 : PeerId → String := fun id => Impl.base58 id.bytes

end Libp2p.Identity.Mock.Keys
