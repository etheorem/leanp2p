import Libp2p.Identity.Constants
import Libp2p.Identity.KeyType
import Bytes
import Proto

/-!
# Key serialization

The peer-ids specification assigns one `Data` representation to each
algorithm. These writers assemble those representations from key material;
they do not generate keys or check cryptographic content. DER INTEGERs
are unsigned key components, supplied most-significant byte first.
`Keys` owns validation and calls the shared protobuf field writer below.
-/

set_option autoImplicit false

namespace Libp2p.Identity.Marshal

private def bigEndian (n : Nat) : List UInt8 :=
  if n < 256 then [UInt8.ofNat n]
  else bigEndian (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n

-- DER uses one length byte below 128; larger lengths carry their byte count.
private def derLength (n : Nat) : ByteArray :=
  if n < 128 then ByteArray.mk #[UInt8.ofNat n]
  else
    let digits := bigEndian n
    ByteArray.mk ((UInt8.ofNat (128 + digits.length) :: digits).toArray)

private def der (tag : UInt8) (content : ByteArray) : ByteArray :=
  ByteArray.mk #[tag] ++ derLength content.size ++ content

private def derInteger (raw : ByteArray) : ByteArray :=
  let digits := raw.toList.dropWhile (· == 0)
  let digits := if digits.isEmpty then [0] else digits
  -- DER INTEGER is signed: prepend zero when an unsigned component's top bit is set.
  let digits := if 128 ≤ digits.head! then 0 :: digits else digits
  der 0x02 (ByteArray.mk digits.toArray)

private def bitString (raw : ByteArray) : ByteArray :=
  der 0x03 (ByteArray.mk #[0] ++ raw)

/-- Preferred Ed25519 private `Data`: seed followed by its public key.
The caller obtains the public key through the crypto facade. -/
def ed25519PrivateData (seed publicKey : ByteArray) : ByteArray :=
  seed ++ publicKey

/-- SEC1 compressed point: parity byte, then the big-endian x coordinate. -/
def secp256k1PublicData (oddY : Bool) (x : ByteArray) : ByteArray :=
  ByteArray.mk #[if oddY then 0x03 else 0x02] ++ x

/-- RSA public `Data` as SPKI DER, wrapping the PKCS#1 modulus and exponent. -/
def rsaPublicData (modulus exponent : ByteArray) : ByteArray :=
  der 0x30 (rsaAlgorithmIdentifier ++
    bitString (der 0x30 (derInteger modulus ++ derInteger exponent)))

/-- RSA private `Data` as PKCS#1 DER. Components are n, e, d, p, q,
d mod (p-1), d mod (q-1), and q inverse mod p, in that order. -/
def rsaPrivateData (components : Vector ByteArray 8) : ByteArray :=
  der 0x30 (derInteger ByteArray.empty ++
    components.toArray.foldl (fun bytes component => bytes ++ derInteger component) ByteArray.empty)

/-- P-256 public `Data` as SPKI DER with an uncompressed SEC1 point. -/
def ecdsaPublicData (x y : ByteArray) : ByteArray :=
  der 0x30 (ecAlgorithmIdentifier ++ bitString (ByteArray.mk #[0x04] ++ x ++ y))

/-- P-256 private `Data` as SEC1 DER, including the curve and public point. -/
def ecdsaPrivateData (scalar x y : ByteArray) : ByteArray :=
  der 0x30 (derInteger (ByteArray.mk #[1]) ++ der 0x04 scalar ++
    der 0xa0 p256CurveIdentifier ++ der 0xa1 (bitString (ByteArray.mk #[0x04] ++ x ++ y)))

/-- Public `Data` already has the form the backend verifier loads. -/
def publicBackendData (_keyType : KeyType) (raw : ByteArray) : ByteArray := raw

/-- The backend loads an Ed25519 seed, not the stored seed/public envelope.
Other algorithms already carry the scalar or DER their loaders accept. -/
def privateBackendData (keyType : KeyType) (raw : ByteArray) : ByteArray :=
  match keyType with
  | .ed25519 => raw.extract 0 ed25519KeySize
  | .secp256k1 | .ecdsa | .rsa => raw

/-- Common key fields, always Type followed by Data.
The proof argument lets protobuf encoding remain total on checked keys. -/
def keyFields (keyType : KeyType) (raw : ByteArray)
    (wireValid : (Pb.Value.bytes (Bytes.toNatList raw)).Valid) : Pb.Fields :=
  ⟨[(1, .varint keyType.toCode), (2, .bytes (Bytes.toNatList raw))], by
    intro entry h
    simp at h
    rcases h with rfl | rfl
    · change 0 < 1 ∧ 1 < Pb.fieldNumberLimit ∧ (Pb.Value.varint keyType.toCode).Valid
      refine ⟨by decide, by decide, ?_⟩
      cases keyType <;> decide
    · change 0 < 2 ∧ 2 < Pb.fieldNumberLimit ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid
      exact ⟨by decide, by decide, wireValid⟩⟩

/-- Serialize the complete key through the shared protobuf encoder. -/
def key (keyType : KeyType) (raw : ByteArray)
    (wireValid : (Pb.Value.bytes (Bytes.toNatList raw)).Valid) : ByteArray :=
  Pb.encodeFieldsB (keyFields keyType raw wireValid)

end Libp2p.Identity.Marshal
