import Crypto
import Libp2p.Identity.Constants
import Libp2p.Identity.KeyType

/-!
# The per-type `Data` forms

The peer-ids spec carries every key in a `Keys` protobuf (`Type`, then
`Data`), and each key type fixes the form of its `Data` (the package
ARCHITECTURE, "Public surface"). This module holds those forms: which
sizes and shells a key type accepts, and the Ed25519 envelope, the
64-byte seed‖public form. The backend takes and gives the raw forms,
and this module turns one into the other (§4.6; the backend
ARCHITECTURE, "Decisions"). The message itself and its `ProtoMessage`
instance live in `Libp2p.Identity.Keys`.
-/

set_option autoImplicit false

namespace Libp2p.Identity

/-- The DER shell of the package ARCHITECTURE, owned contract 2: at
least `derMinBytes`, and a leading SEQUENCE tag. The DER content is the
verifier's check behind the facade (§4.6); a full parse here would be a
second DER parser. -/
def derShell (d : ByteArray) : Bool :=
  derMinBytes ≤ d.size && d[0]? == some derSequenceTag

/-- A compressed SEC1 point: 33 bytes, the tag `0x02` or `0x03` by the
parity of y (SEC 1 §2.3.3). -/
def isCompressedPoint (d : ByteArray) : Bool :=
  d.size == secp256k1PubBytes && (d[0]? == some 0x02 || d[0]? == some 0x03)

/-- The public `Data` a key type holds: the raw size of Ed25519, the
compressed point form of secp256k1, and the DER shell of an SPKI key.
The point itself is the verifier's check behind the facade, as the DER
content is (owned contract 2). -/
def pubDataFits : KeyType → ByteArray → Bool
  | .ed25519, d => d.size == ed25519PubBytes
  | .secp256k1, d => isCompressedPoint d
  | .ecdsa, d => derShell d
  | .rsa, d => derShell d

/-- The private `Data` a key type holds. Ed25519 holds the canonical
64-byte envelope only; the strict unmarshal turns the 32-byte seed and
the legacy 96-byte form into it. ECDSA holds a SEC1 or a PKCS#8 key, and
RSA a PKCS#1 key; both pass as a DER shell, and the backend loads them. -/
def privDataFits : KeyType → ByteArray → Bool
  | .ed25519, d => d.size == ed25519PrivBytes
  | .secp256k1, d => d.size == secp256k1PrivBytes
  | .ecdsa, d => derShell d
  | .rsa, d => derShell d

/-- The Ed25519 envelope: the seed, then the public key. -/
def ed25519Envelope (seed pub : Crypto.Key32) : ByteArray :=
  seed.bytes ++ pub.bytes

/-- The envelope is always 64 bytes, so a key built from it fits
`privDataFits` with no runtime check. -/
theorem sizeEd25519Envelope (seed pub : Crypto.Key32) :
    (ed25519Envelope seed pub).size = ed25519PrivBytes := by
  simp [ed25519Envelope, ByteArray.size_append, seed.sizeEq, pub.sizeEq, ed25519PrivBytes,
    ed25519SeedBytes, ed25519PubBytes]

/-- The seed of an Ed25519 envelope: its first 32 bytes, the key the
backend signs with. The size proof comes from the envelope's size, so
the backend gets a `Key32` with no check (§3.7). -/
def ed25519Seed (d : ByteArray) (h : d.size = ed25519PrivBytes) : Crypto.Key32 where
  bytes := d.extract 0 ed25519SeedBytes
  sizeEq := by
    simp [ByteArray.size_extract, h, ed25519PrivBytes, ed25519SeedBytes, ed25519PubBytes]

end Libp2p.Identity
