/-!
# Key-format constants

Sizes of the per-type `Data` forms in the peer-ids specification.
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

end Libp2p.Identity
