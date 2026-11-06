/-!
# Identity constants

Key Data forms from the peer-ids specification, and ENR fields from
EIP-778. Key names are ASCII bytes over the byte model.
-/

set_option autoImplicit false

namespace Libp2p.Identity

def ed25519KeySize : Nat := 32
def ed25519PrivateSize : Nat := 2 * ed25519KeySize
def ed25519LegacyPrivateSize : Nat := 3 * ed25519KeySize
def secp256k1PublicSize : Nat := 33
def secp256k1PrivateSize : Nat := 32
def minDerSize : Nat := 8

/-- The complete public-key protobuf inlines through this inclusive boundary. -/
def maxInlineKeySize : Nat := 42

/-- SHA-256's output length, used by the peer-multihash validity rule. -/
def peerIdDigestSize : Nat := 32

/-- Bound text before base conversion allocates or constructs a large integer. -/
def maxPeerIdTextSize : Nat := 4096

/-- DER AlgorithmIdentifier for rsaEncryption, including its NULL parameter. -/
def rsaAlgorithmIdentifier : ByteArray := ByteArray.mk #[
  0x30, 0x0d, 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01, 0x05, 0x00]

/-- DER OID for the named P-256 curve (prime256v1). -/
def p256CurveIdentifier : ByteArray := ByteArray.mk #[
  0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]

/-- DER AlgorithmIdentifier for id-ecPublicKey with the P-256 parameter. -/
def ecAlgorithmIdentifier : ByteArray :=
  ByteArray.mk #[0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01] ++
    p256CurveIdentifier

namespace Enr

/-- The largest encoded record, in bytes. EIP-778, "RLP Encoding":
"Implementations should reject records larger than this size." -/
def maxRecordSize : Nat := 300

/-- The `v4` signature: `r ‖ s`, 32 bytes each, with no recovery id. -/
def signatureSize : Nat := 64

/-- The `secp256k1` value: a compressed point. -/
def publicKeySize : Nat := secp256k1PublicSize

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
