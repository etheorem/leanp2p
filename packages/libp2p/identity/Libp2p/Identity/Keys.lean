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

/-- The DER shell gate; private-key constructors also call the facade's loader. -/
def derDataValid (raw : ByteArray) : Prop :=
  minDerSize ≤ raw.size ∧ raw[0]? = some 0x30

instance (raw : ByteArray) : Decidable (derDataValid raw) :=
  inferInstanceAs (Decidable (minDerSize ≤ raw.size ∧ raw[0]? = some 0x30))

/-- The public Data shape required by each algorithm. -/
def pubKeyDataValid (keyType : KeyType) (raw : ByteArray) : Prop :=
  match keyType with
  | .ed25519 => raw.size = ed25519KeySize
  | .secp256k1 => raw.size = secp256k1PublicSize ∧ (raw[0]? = some 2 ∨ raw[0]? = some 3)
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

/-- Constructors hold Ed25519 seed/public envelopes, SEC1, or PKCS#1 for export. -/
structure PrivKey where
  private mk ::
  keyType : KeyType
  raw : ByteArray
  valid : privKeyDataValid keyType raw ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid

/-- Construct from public Data after checking its shape and encoding budget. -/
def PubKey.ofData? (keyType : KeyType) (raw : ByteArray) : Except Error PubKey :=
  if h : pubKeyDataValid keyType raw ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid then
    .ok ⟨keyType, raw, h⟩
  else .error (.invalidKeyData keyType raw.size)

private def PrivKey.checked (keyType : KeyType) (raw : ByteArray) : Except Error PrivKey :=
  if h : privKeyDataValid keyType raw ∧ (Pb.Value.bytes (Bytes.toNatList raw)).Valid then
    .ok ⟨keyType, raw, h⟩
  else .error (.invalidKeyData keyType raw.size)

/-- Accept seeds and both envelopes, check their public halves, and hold 64 bytes. -/
private def PrivKey.ofEd25519? (raw : ByteArray) : Except Error PrivKey := do
  if h : raw.size = ed25519KeySize ∨ raw.size = ed25519PrivateSize ∨
      raw.size = ed25519LegacyPrivateSize then
    let seed : Crypto.Key32 := ⟨raw.extract 0 ed25519KeySize, by
      simp only [ByteArray.size_extract, Nat.sub_zero]
      simp only [ed25519KeySize, ed25519PrivateSize, ed25519LegacyPrivateSize] at h ⊢
      omega⟩
    let publicKey ← (Crypto.ed25519PublicKey seed).mapError Error.crypto
    if raw.size != ed25519KeySize then
      if raw.extract ed25519KeySize ed25519PrivateSize != publicKey.bytes then
        throw .publicMismatch
      if raw.size == ed25519LegacyPrivateSize &&
          raw.extract ed25519PrivateSize ed25519LegacyPrivateSize != publicKey.bytes then
        throw .publicMismatch
    checked .ed25519 (Marshal.ed25519PrivateData seed.bytes publicKey.bytes)
  else throw (.invalidKeyData .ed25519 raw.size)

/-- Validate through the facade and hold the private DER form required by libp2p.
P-256 accepts PKCS#8 imports. RSA accepts its specified PKCS#1 form only. -/
private def PrivKey.ofDer? (keyType : KeyType) (raw : ByteArray)
    (reencode : ByteArray → Except Crypto.CryptoError ByteArray)
    (allowImport : Bool) : Except Error PrivKey := do
  if ¬ derDataValid raw then throw (.invalidKeyData keyType raw.size)
  let canonical ← (reencode raw).mapError Error.crypto
  if !allowImport && canonical != raw then throw (.invalidKeyData keyType raw.size)
  checked keyType canonical

/-- Validate private Data and normalize accepted imports to the wire export form. -/
def PrivKey.ofData? (keyType : KeyType) (raw : ByteArray) : Except Error PrivKey :=
  match keyType with
  | .ed25519 => ofEd25519? raw
  | .secp256k1 => checked keyType raw
  | .ecdsa => ofDer? keyType raw Crypto.p256Sec1 true
  | .rsa => ofDer? keyType raw Crypto.rsaPkcs1 false

instance : Pb.ProtoMessage PubKey where
  toFields key := Marshal.keyFields key.keyType key.raw key.valid.2
  ofFields? fields := (Unmarshal.keyFields? PubKey.ofData? fields).mapError Error.toProtobuf

instance : Pb.ProtoMessage PrivKey where
  toFields key := Marshal.keyFields key.keyType key.raw key.valid.2
  ofFields? fields := (Unmarshal.keyFields? PrivKey.ofData? fields).mapError Error.toProtobuf

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
def PrivKey.sign (key : PrivKey) (msg : ByteArray) : ExceptT Error IO ByteArray :=
  match h : key.keyType with
  | .ed25519 => ExceptT.mk (pure ((Crypto.ed25519Sign (key.ed25519Seed h) msg).mapError .crypto))
  | .secp256k1 =>
      ExceptT.mk (pure ((Crypto.secp256k1Sign (key.secp256k1Scalar h) msg).mapError .crypto))
  | .rsa => ExceptT.mk (pure ((Crypto.rsaSign key.backendData msg).mapError .crypto))
  | .ecdsa => (Crypto.p256Sign key.backendData msg).adapt .crypto

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
public Data crosses its own checked boundary and retains validation errors.
-/
def derivePubKey (key : PrivKey) : Except Error PubKey := do
  let raw : ByteArray ← (match h : key.keyType with
    | .ed25519 =>
        (Crypto.ed25519PublicKey (key.ed25519Seed h)).map
          (fun (publicKey : Crypto.Key32) => publicKey.bytes)
    | .secp256k1 =>
        Crypto.secp256k1PublicKey (key.secp256k1Scalar h)
    | .rsa => Crypto.rsaPublicKey key.backendData
    | .ecdsa => Crypto.p256PublicKey key.backendData).mapError Error.crypto
  PubKey.ofData? key.keyType raw

/-- Serialize a checked public key with the fixed Type/Data field order. -/
def marshalPubKey (key : PubKey) : ByteArray :=
  Marshal.key key.keyType key.raw key.valid.2

/-- Serialize a private key in its canonical libp2p Data representation. -/
def marshalPrivKey (key : PrivKey) : ByteArray :=
  Marshal.key key.keyType key.raw key.valid.2

/-- The public wrapper and generic protobuf encoder share exactly one field writer. -/
theorem marshalPubKey_eq_encodeMessageB (key : PubKey) :
    marshalPubKey key = Pb.encodeMessageB key := rfl

/-- The private wrapper and generic protobuf encoder share exactly one field writer. -/
theorem marshalPrivKey_eq_encodeMessageB (key : PrivKey) :
    marshalPrivKey key = Pb.encodeMessageB key := rfl

/-- Decode a complete public-key message through its checked constructor. -/
def unmarshalPubKey? (bytes : ByteArray) : Except Error PubKey := Unmarshal.key? PubKey.ofData? bytes

/-- Decode a complete private-key message through its checked constructor. -/
def unmarshalPrivKey? (bytes : ByteArray) : Except Error PrivKey :=
  Unmarshal.key? PrivKey.ofData? bytes

/-- The public key's checked fields reconstruct the same value. -/
theorem PubKey.ofFieldsToFields (key : PubKey) :
    Pb.ProtoMessage.ofFields? (Pb.ProtoMessage.toFields key) = .ok key := by
  change (Unmarshal.keyFields? PubKey.ofData?
    (Marshal.keyFields key.keyType key.raw key.valid.2)).mapError Error.toProtobuf = .ok key
  rw [Unmarshal.keyFieldsRoundTrip]
  simp [PubKey.ofData?, key.valid, Except.mapError]

/-- Public-key encoding round-trips over the proved protobuf byte model. -/
theorem PubKey.decodeEncode (key : PubKey) :
    Pb.decodeMessage? (Pb.encodeMessage key) = .ok (key, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, bind, Except.bind,
    PubKey.ofFieldsToFields]

end Libp2p.Identity
