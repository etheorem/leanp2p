import Libp2p.Identity.Marshal
import Libp2p.Identity.Unmarshal
import Bytes
import Proto
import Crypto

/-!
# Public and private keys

Keys carry the checked Data shape and the protobuf encoding bound.
The instances emit Type, then Data, through the shared wire codec.
Signing, verification, and public-key derivation use the Crypto facade.
-/

set_option autoImplicit false

namespace Libp2p.Identity

/-- Only the DER shell is checked here; the crypto facade checks its content. -/
def derDataValid (raw : ByteArray) : Prop :=
  minDerSize ≤ raw.size ∧ raw[0]? = some 0x30

instance (raw : ByteArray) : Decidable (derDataValid raw) :=
  inferInstanceAs (Decidable (minDerSize ≤ raw.size ∧ raw[0]? = some 0x30))

/-- The public Data shape required by each algorithm. -/
def pubKeyDataValid (keyType : KeyType) (raw : ByteArray) : Prop :=
  match keyType with
  | .ed25519 => raw.size = ed25519KeySize
  | .secp256k1 => raw.size = secp256k1PublicSize
  | .ecdsa | .rsa => derDataValid raw

instance (keyType : KeyType) (raw : ByteArray) : Decidable (pubKeyDataValid keyType raw) := by
  cases keyType <;> unfold pubKeyDataValid <;> infer_instance

/-- Accepted private Data forms, including the checked legacy Ed25519 copies. -/
def privKeyDataValid (keyType : KeyType) (raw : ByteArray) : Prop :=
  match keyType with
  | .ed25519 =>
      raw.size = ed25519KeySize ∨ raw.size = ed25519PrivateSize ∨
        (raw.size = ed25519LegacyPrivateSize ∧
          raw.extract ed25519KeySize ed25519PrivateSize =
            raw.extract ed25519PrivateSize ed25519LegacyPrivateSize)
  | .secp256k1 => raw.size = secp256k1PrivateSize
  | .ecdsa | .rsa => derDataValid raw

instance (keyType : KeyType) (raw : ByteArray) : Decidable (privKeyDataValid keyType raw) := by
  cases keyType <;> unfold privKeyDataValid <;> infer_instance

/-- A public key carries its algorithm's Data-shape and encoding-bound proofs. -/
structure PubKey where
  keyType : KeyType
  raw : ByteArray
  valid : pubKeyDataValid keyType raw ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid

/-- A private key retains its accepted Data representation after construction. -/
structure PrivKey where
  keyType : KeyType
  raw : ByteArray
  valid : privKeyDataValid keyType raw ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid

/-- Construct from public Data after checking its shape and encoding budget. -/
def PubKey.ofData? (keyType : KeyType) (raw : ByteArray) : Option PubKey :=
  if h : pubKeyDataValid keyType raw ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid then
    some ⟨keyType, raw, h⟩
  else none

/-- Construct from private Data; legacy Ed25519 copies must agree. -/
def PrivKey.ofData? (keyType : KeyType) (raw : ByteArray) : Option PrivKey :=
  if h : privKeyDataValid keyType raw ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid then
    some ⟨keyType, raw, h⟩
  else none

instance : Pb.ProtoMessage PubKey where
  toFields key := Marshal.keyFields key.keyType key.raw key.valid.2
  ofFields? := Unmarshal.keyFields? PubKey.ofData?

instance : Pb.ProtoMessage PrivKey where
  toFields key := Marshal.keyFields key.keyType key.raw key.valid.2
  ofFields? := Unmarshal.keyFields? PrivKey.ofData?

/-- Public Data bytes for the backend verifier, without repeated validation. -/
def PubKey.backendData (key : PubKey) : ByteArray :=
  Marshal.publicBackendData key.keyType key.raw

/-- Seed, scalar, or DER for the backend signer, without repeated validation. -/
def PrivKey.backendData (key : PrivKey) : ByteArray :=
  Marshal.privateBackendData key.keyType key.raw

private theorem ed25519BackendDataSize (key : PrivKey) (h : key.keyType = .ed25519) :
    key.backendData.size = ed25519KeySize := by
  have valid := key.valid.1
  simp only [privKeyDataValid, h] at valid
  have enough : ed25519KeySize ≤ key.raw.size := by
    rcases valid with size | size | ⟨size, _⟩
    · omega
    · simp only [ed25519PrivateSize] at size
      omega
    · simp only [ed25519LegacyPrivateSize] at size
      omega
  simp [PrivKey.backendData, Marshal.privateBackendData, h,
    ByteArray.size_extract, Nat.min_eq_left enough]

private def PrivKey.ed25519Seed (key : PrivKey) (h : key.keyType = .ed25519) : Crypto.Key32 :=
  ⟨key.backendData, by
    simpa only [ed25519KeySize] using ed25519BackendDataSize key h⟩

private def PrivKey.secp256k1Scalar (key : PrivKey) (h : key.keyType = .secp256k1) :
    Crypto.Key32 :=
  ⟨key.backendData, by
    have valid := key.valid.1
    simpa only [privKeyDataValid, h, secp256k1PrivateSize,
      PrivKey.backendData, Marshal.privateBackendData] using valid⟩

/-- Sign the original message through the crypto facade, which owns hashing.
P-256 draws a random nonce, so the common dispatch carries IO. The other
schemes lift their deterministic result into the same error-preserving surface.
-/
def PrivKey.sign (key : PrivKey) (msg : ByteArray) : ExceptT Crypto.CryptoError IO ByteArray :=
  match h : key.keyType with
  | .ed25519 => ExceptT.mk (pure (Crypto.ed25519Sign (key.ed25519Seed h) msg))
  | .secp256k1 => ExceptT.mk (pure (Crypto.secp256k1Sign (key.secp256k1Scalar h) msg))
  | .rsa => ExceptT.mk (pure (Crypto.rsaSign key.backendData msg))
  | .ecdsa => Crypto.p256Sign key.backendData msg

/-- Verify through the facade's scheme for this key type. Every verifier is
deterministic and returns false for malformed inputs or a signature mismatch.
-/
def PubKey.verify (key : PubKey) (msg sig : ByteArray) : Bool :=
  match key.keyType with
  | .ed25519 => Crypto.ed25519Verify key.backendData msg sig
  | .secp256k1 => Crypto.secp256k1Verify key.backendData msg sig
  | .rsa => Crypto.rsaVerify key.backendData msg sig
  | .ecdsa => Crypto.p256Verify key.backendData msg sig

/-- Derive the public key through the crypto facade for the private key's type.
The checked private key supplies the seed/scalar size proofs. The returned
public Data crosses its own checked boundary; an unexpected shape is a fault.
-/
def derivePubKey (key : PrivKey) : Except Crypto.CryptoError PubKey := do
  let raw : ByteArray ← match h : key.keyType with
    | .ed25519 =>
        (Crypto.ed25519PublicKey (key.ed25519Seed h)).map (·.bytes)
    | .secp256k1 =>
        Crypto.secp256k1PublicKey (key.secp256k1Scalar h)
    | .rsa => Crypto.rsaPublicKey key.backendData
    | .ecdsa => Crypto.p256PublicKey key.backendData
  match PubKey.ofData? key.keyType raw with
  | some publicKey => return publicKey
  | none => throw .fault

/-- Serialize a checked public key with the fixed Type/Data field order. -/
def marshalPubKey (key : PubKey) : ByteArray :=
  Marshal.key key.keyType key.raw key.valid.2

/-- Serialize a checked private key, retaining the accepted Data representation. -/
def marshalPrivKey (key : PrivKey) : ByteArray :=
  Marshal.key key.keyType key.raw key.valid.2

/-- The public wrapper and generic protobuf encoder share exactly one field writer. -/
theorem marshalPubKey_eq_encodeMessageB (key : PubKey) :
    marshalPubKey key = Pb.encodeMessageB key := rfl

/-- The private wrapper and generic protobuf encoder share exactly one field writer. -/
theorem marshalPrivKey_eq_encodeMessageB (key : PrivKey) :
    marshalPrivKey key = Pb.encodeMessageB key := rfl

/-- Decode a complete public-key message through its checked constructor. -/
def unmarshalPubKey? (bytes : ByteArray) : Except Pb.Error PubKey := Unmarshal.key? bytes

/-- Decode a complete private-key message through its checked constructor. -/
def unmarshalPrivKey? (bytes : ByteArray) : Except Pb.Error PrivKey := Unmarshal.key? bytes

end Libp2p.Identity
