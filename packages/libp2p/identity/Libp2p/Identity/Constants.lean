/-!
# The identity constants

The numbers of the peer-ids spec that this package checks, each with
one home (PRINCIPLES 1.5). The spec fixes the field numbers of the
`Keys` message, the per-type `Data` sizes, and the inlining threshold
of the peer id. The DER shell minimum comes from the package
ARCHITECTURE, owned contract 2.
-/

set_option autoImplicit false

namespace Libp2p.Identity

/-! ## The `Keys` message -/

/-- The field number of `Type` in the `PublicKey` and `PrivateKey`
messages: `required KeyType Type = 1`. -/
def keysTypeField : Nat := 1

/-- The field number of `Data`: `required bytes Data = 2`. -/
def keysDataField : Nat := 2

/-! ## The per-type `Data` sizes -/

/-- An Ed25519 public key: the raw 32-byte point (RFC 8032 §5.1.5). -/
def ed25519PubBytes : Nat := 32

/-- An Ed25519 seed, the first half of the private `Data`. -/
def ed25519SeedBytes : Nat := 32

/-- The canonical Ed25519 private `Data`: the seed, then the public key.
The peer-ids spec vector carries this form, and go-libp2p stores it
(`vendor/go-libp2p/core/crypto/ed25519.go`, lines 139 and 140). -/
def ed25519PrivBytes : Nat := ed25519SeedBytes + ed25519PubBytes

/-- The legacy Ed25519 private `Data`: the seed and the public key, then
a redundant copy of the public key
(`vendor/go-libp2p/core/crypto/ed25519.go`, line 132). The strict
unmarshal accepts it and drops the copy. -/
def ed25519LegacyPrivBytes : Nat := ed25519PrivBytes + ed25519PubBytes

/-- A secp256k1 public key: the SEC1 compressed point, a parity byte
and the 32-byte x coordinate. -/
def secp256k1PubBytes : Nat := 33

/-- A secp256k1 private key: the raw 32-byte scalar. -/
def secp256k1PrivBytes : Nat := 32

/-- The smallest DER key the shell check passes (owned contract 2). -/
def derMinBytes : Nat := 8

/-- The tag of a DER SEQUENCE (X.690 §8.9), the first byte of every
SPKI, PKCS#1, SEC1, and PKCS#8 key. -/
def derSequenceTag : UInt8 := 0x30

/-! ## The peer id -/

/-- The largest marshaled public key that inlines as an identity
multihash; a longer key hashes with sha2-256 (the peer-ids spec,
"Peer Ids"; go-libp2p `maxInlineKeyLength`, `len(b) <=
maxInlineKeyLength`). A key at the threshold inlines. -/
def maxInlineKeyBytes : Nat := 42

end Libp2p.Identity
