/-!
# The constants of `libp2p/identity`

One home per fact (PRINCIPLES 1.5, root ARCHITECTURE §3.8). This file
holds the ENR side of the package. W5.1 adds the key side: the 42-byte
inlining threshold, the per-type `Data` lengths, and the DER minima.

The ENR facts come from EIP-778 (`vendor/eips/EIPS/eip-778.md`). The
key names are their ASCII bytes over the byte model.
-/

set_option autoImplicit false

namespace Libp2p.Identity

namespace Enr

/-- The largest encoded record, in bytes. EIP-778, "RLP Encoding":
"Implementations should reject records larger than this size." -/
def maxRecordSize : Nat := 300

/-- The `v4` signature: `r ‖ s`, 32 bytes each, with no recovery id. -/
def signatureSize : Nat := 64

/-- The `secp256k1` value: a compressed point. -/
def publicKeySize : Nat := 33

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
