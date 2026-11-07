/-!
# The identity constants

The numbers that this package checks, each with one home (PRINCIPLES
1.5, root ARCHITECTURE §3.8). The peer-ids spec fixes the field
numbers of the `Keys` message, the per-type `Data` sizes, and the
inlining threshold of the peer id. The DER shell minimum comes from the
package ARCHITECTURE, owned contract 2.

The ENR facts come from EIP-778 (`vendor/eips/EIPS/eip-778.md`). The
key names are their ASCII bytes over the byte model.
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

/-! ## The ENR -/

namespace Enr

/-- The largest encoded record, in bytes. EIP-778, "RLP Encoding":
"Implementations should reject records larger than this size." -/
def maxRecordSize : Nat := 300

/-- The `v4` signature: `r ‖ s`, 32 bytes each, with no recovery id. -/
def signatureSize : Nat := 64

/-- The `secp256k1` value: a compressed point. -/
def publicKeySize : Nat := secp256k1PubBytes

/-- `seq` is a 64-bit unsigned integer. -/
def seqBytes : Nat := 8

/-- A port is a 16-bit big-endian integer. -/
def portBytes : Nat := 2

/-- The `ip` value: an IPv4 address. -/
def ip4Size : Nat := 4

/-- The `ip6` value: an IPv6 address. -/
def ip6Size : Nat := 16

/-- Half the secp256k1 group order. A `v4` signature with `s` above
it is the high-S twin of another, and the verifier refuses it, as
go-ethereum and sigp/enr do (package ARCHITECTURE, contract 5). -/
def halfOrder : Nat := 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0

/-! ## Key names -/

/-- `id`: the name of the identity scheme. -/
def nameId : List Nat := [0x69, 0x64]

/-- `secp256k1`: the compressed public key. -/
def nameSecp256k1 : List Nat := [0x73, 0x65, 0x63, 0x70, 0x32, 0x35, 0x36, 0x6b, 0x31]

/-- `ip`: the IPv4 address. -/
def nameIp : List Nat := [0x69, 0x70]

/-- `tcp`: the TCP port. -/
def nameTcp : List Nat := [0x74, 0x63, 0x70]

/-- `udp`: the UDP port. -/
def nameUdp : List Nat := [0x75, 0x64, 0x70]

/-- `ip6`: the IPv6 address. -/
def nameIp6 : List Nat := [0x69, 0x70, 0x36]

/-- `tcp6`: the IPv6-specific TCP port. -/
def nameTcp6 : List Nat := [0x74, 0x63, 0x70, 0x36]

/-- `udp6`: the IPv6-specific UDP port. -/
def nameUdp6 : List Nat := [0x75, 0x64, 0x70, 0x36]

/-- `v4`: the one identity scheme EIP-778 defines. -/
def schemeV4 : List Nat := [0x76, 0x34]

/-- The prefix of the text form. EIP-778, "RLP Encoding": "The textual
form of a node record is the base64 encoding of its RLP
representation, prefixed by `enr:`." -/
def textPrefix : String := "enr:"

end Enr

end Libp2p.Identity
