import Proto
import Libp2p.Identity.Error
import Libp2p.Identity.Marshal

/-!
# Keys

The `Keys` protobuf message, the `PubKey` and `PrivKey` types over it,
and the sign, verify, and derive dispatch to the `Crypto` facade.

**The message.** The peer-ids spec carries every key, public or
private, in one protobuf shape (go-libp2p `core/crypto/pb/crypto.proto`):

```
message PublicKey  { required KeyType Type = 1; required bytes Data = 2; }
message PrivateKey { required KeyType Type = 1; required bytes Data = 2; }
```

The two messages share the field table, so `Keys` is one type with one
`ProtoMessage` instance (ARCHITECTURE §3.2). The spec asks for a
deterministic encoding, and the instance gives one by construction:
`toFields` emits `Type`, then `Data`, and `codec/proto` writes minimal
varints (owned contract 1). The Ed25519 public key of the spec vector
shows the layout:

```
08 01        field 1 (Type), wire type VARINT: KeyType 1, Ed25519
12 20 …      field 2 (Data), wire type LEN: 32 bytes of key
```

**The keys.** `PubKey` and `PrivKey` are proof-carrying newtypes over
the message (§3.7): each holds the message and the fact that its `Data`
fits the key type (`pubDataFits`, `privDataFits`). The constructors
check the fact where the bytes enter, so sign, verify, and derive take
it from the type and check nothing again (owned contract 2). A 31-byte
Ed25519 key never becomes a `PubKey`, so no peer id derives from it.

**The schemes** are the peer-ids spec's:

| KeyType | Scheme | Nonce |
|---|---|---|
| Ed25519 | RFC 8032 over the raw message | none |
| secp256k1 | ECDSA over SHA-256(message), BIP-62 low-S, DER signature | random |
| ECDSA | ECDSA P-256 over SHA-256(message), DER signature | random |
| RSA | RSASSA-PKCS1-v1_5 over SHA-256(message) | none |

The backend bindings hash the message themselves, so every call passes
the message. Which schemes draw a nonce is the backend's binding table,
so `sign` runs in `IO` for all four (§3.6). A `match h : k.keyType`
keeps the equation `h` in scope, and `PrivKey.ed25519Seed` turns it
into a `Key32` with no runtime test.
-/

set_option autoImplicit false

namespace Libp2p.Identity

open Bytes

/-! ## The `Keys` message -/

/-- The byte model of `d` has one entry per byte. -/
theorem lengthToNatList (d : ByteArray) : (toNatList d).length = d.size := by
  unfold toNatList
  rw [List.length_map, Array.length_toList]
  rfl

/-- Every entry of the byte model of `d` is a byte. -/
theorem ltOfMemToNatList {d : ByteArray} {x : Nat} (h : x ∈ toNatList d) : x < 256 := by
  simp only [toNatList, List.mem_map] at h
  obtain ⟨b, _, rfl⟩ := h
  exact b.toNat_lt

/-- One `PublicKey` or `PrivateKey` message: the key type and the `Data`
bytes, as the wire carries them. `dataLt` is the varint budget of the
`Data` length prefix (`Pb.Value.Valid`), so `toFields` builds a
`Pb.Fields` with no check. The decoder supplies the fact; Lean erases it
at run time. -/
structure Keys where
  /-- The `Type` field. -/
  keyType : KeyType
  /-- The `Data` field. -/
  data : ByteArray
  /-- The length of `data` fits its varint prefix. -/
  dataLt : data.size < Varint.limit
  deriving DecidableEq

/-- Core Lean gives `ByteArray` no `Repr`, so the instance prints `Data`
as hex text. -/
instance : Repr Keys where
  reprPrec k _ := s!"\{ keyType := {repr k.keyType}, data := {toHex k.data} }"

namespace Keys

/-- The message of a key type and `Data` bytes. `none` only for a `Data`
past the varint budget, which no `ByteArray` in memory reaches. -/
def ofData? (t : KeyType) (d : ByteArray) : Option Keys :=
  if h : d.size < Varint.limit then some ⟨t, d, h⟩ else none

/-- The entries of the message, `Type` first, then `Data`: the emit
order of the field table. `codec/proto` carries a payload in the
`List Nat` byte model, so `Data` enters through `toNatList`. -/
def toFields (k : Keys) : Pb.Fields where
  entries := [
    (keysTypeField, .varint k.keyType.toCode),
    (keysDataField, .bytes (toNatList k.data))]
  valid := by
    -- Each entry has a field number in the spec range and a value in
    -- bounds: the code is below 4, and `k.dataLt` bounds the `Data`
    -- length.
    have hCode := k.keyType.toCodeLt
    have hData := k.dataLt
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl)
    · simp only [Pb.Entry.Valid, Pb.Value.Valid, keysTypeField, Pb.fieldNumberLimit,
        Varint.limit, Varint.maxBytes]
      omega
    · refine ⟨by simp [keysDataField], by simp [keysDataField, Pb.fieldNumberLimit], ?_,
        fun _ hx => ltOfMemToNatList hx⟩
      rw [lengthToNatList]
      exact hData

/-- The message of decoded entries. Both fields are required in the
spec schema, so a missing one is `missingField`. A key-type code outside
the closed set is `badKeyType`, as go-libp2p rejects it
(`vendor/go-libp2p/core/crypto/key.go`, lines 136 to 138). A field that
occurs twice gives its last value (`Pb.getVarint?`, "Last One Wins").
Unknown fields pass, as the Go protobuf runtime keeps them
(`vendor/protobuf-go/internal/impl/decode.go`, lines 218 to 230); the
marshal does not write them. -/
def ofFields? (fs : Pb.Fields) : Except Error Keys := do
  let some code := Pb.getVarint? keysTypeField fs | throw (.missingField keysTypeField)
  let some t := KeyType.ofCode? code | throw (.badKeyType code)
  let some d := Pb.getBytes? keysDataField fs | throw (.missingField keysDataField)
  -- A decoded payload is in bounds (`Pb.Fields.valid`), so this branch
  -- never fails; the check gives `dataLt` its proof.
  match ofData? t (ofNatList d) with
  | some k => return k
  | none => throw (.keyData t d.length)

/-- The table reads back its own entries. The `ProtoMessage` instances
of `PubKey` and `PrivKey` build their round trip on it. -/
theorem ofFieldsToFields (k : Keys) : ofFields? (toFields k) = .ok k := by
  simp [ofFields?, toFields, ofData?, Pb.getVarint?, Pb.getBytes?, Pb.lookupLast, List.lookup,
    keysTypeField, keysDataField, KeyType.ofCodeToCode, ofNatListToNatList, k.dataLt]
  -- `simp` leaves `pure ⟨k.keyType, k.data, _⟩ = .ok k`: `pure` of
  -- `Except` is `.ok`, and structure eta rebuilds `k`, so both sides
  -- are defeq.
  rfl

end Keys

/-! ## The key types -/

/-- A public key whose `Data` fits its key type. -/
structure PubKey where
  /-- The message, as `marshal` writes it. -/
  keys : Keys
  /-- The `Data` fits the key type. -/
  fits : pubDataFits keys.keyType keys.data = true
  deriving DecidableEq, Repr

/-- A private key whose `Data` fits its key type. An Ed25519 key holds
the canonical 64-byte envelope. -/
structure PrivKey where
  /-- The message, as `marshal` writes it. -/
  keys : Keys
  /-- The `Data` fits the key type. -/
  fits : privDataFits keys.keyType keys.data = true
  deriving DecidableEq, Repr

namespace PubKey

/-- The key type. -/
def keyType (k : PubKey) : KeyType := k.keys.keyType

/-- The `Data` bytes: the raw key or the SPKI DER. -/
def data (k : PubKey) : ByteArray := k.keys.data

/-- The public key of a message, when its `Data` fits the key type. -/
def ofKeys? (keys : Keys) : Except Error PubKey :=
  if h : pubDataFits keys.keyType keys.data then .ok ⟨keys, h⟩
  else .error (.keyData keys.keyType keys.data.size)

/-- The public key of a key type and its `Data` bytes. -/
def ofData? (t : KeyType) (d : ByteArray) : Except Error PubKey :=
  match Keys.ofData? t d with
  | some keys => ofKeys? keys
  | none => .error (.keyData t d.size)

/-- The Ed25519 public key of a backend key. -/
def ofEd25519 (pub : Crypto.Key32) : PubKey where
  keys := {
    keyType := .ed25519
    data := pub.bytes
    dataLt := by rw [pub.sizeEq]; simp [Varint.limit, Varint.maxBytes] }
  fits := by simp [pubDataFits, pub.sizeEq, ed25519PubBytes]

/-- The deterministic marshaling: the message, `Type` then `Data`,
through the shared field table (owned contract 1). The peer id derives
from these bytes. -/
def marshal (k : PubKey) : ByteArray := Pb.encodeFieldsB k.keys.toFields

/-- Verify a signature of `msg` under the key. `false` covers a
signature that does not verify and every malformed input: the facade
verifiers fold both, fail-closed (§3.6). The secp256k1 verifier rejects
a high S, and the RSA verifier a key outside 2048 to 8192 bits (§4.6). -/
def verify (k : PubKey) (msg sig : ByteArray) : Bool :=
  match k.keyType with
  | .ed25519 => Crypto.ed25519Verify k.data msg sig
  | .secp256k1 => Crypto.secp256k1Verify k.data msg sig
  | .ecdsa => Crypto.p256Verify k.data msg sig
  | .rsa => Crypto.rsaVerify k.data msg sig

end PubKey

namespace PrivKey

/-- The key type. -/
def keyType (k : PrivKey) : KeyType := k.keys.keyType

/-- The `Data` bytes: the Ed25519 envelope, the secp256k1 scalar, or the
DER key. -/
def data (k : PrivKey) : ByteArray := k.keys.data

/-- The private key of a message whose `Data` already has the held
form: the size or shell check of `privDataFits`, and nothing more. -/
private def ofHeld? (keys : Keys) : Except Error PrivKey :=
  if h : privDataFits keys.keyType keys.data then .ok ⟨keys, h⟩
  else .error (.keyData keys.keyType keys.data.size)

/-- The `Data` size of an Ed25519 key, read from the proof field. -/
theorem sizeOfEd25519 {k : PrivKey} (h : k.keyType = .ed25519) :
    k.data.size = ed25519PrivBytes := by
  have hf := k.fits
  -- `keyType` and `data` are projections of `keys`, so `h` rewrites the
  -- key type inside `fits`, and `privDataFits` reduces to a size test.
  simp only [keyType] at h
  rw [h] at hf
  simpa [privDataFits, data] using hf

/-- The `Data` size of a secp256k1 key, read from the proof field. -/
theorem sizeOfSecp256k1 {k : PrivKey} (h : k.keyType = .secp256k1) :
    k.data.size = secp256k1PrivBytes := by
  have hf := k.fits
  simp only [keyType] at h
  rw [h] at hf
  simpa [privDataFits, data] using hf

/-- The Ed25519 seed the backend signs with. -/
def ed25519Seed (k : PrivKey) (h : k.keyType = .ed25519) : Crypto.Key32 :=
  Identity.ed25519Seed k.data (sizeOfEd25519 h)

/-- The secp256k1 scalar the backend signs with. -/
def secp256k1Scalar (k : PrivKey) (h : k.keyType = .secp256k1) : Crypto.Key32 :=
  ⟨k.data, by simpa [secp256k1PrivBytes] using sizeOfSecp256k1 h⟩

/-- The Ed25519 private key of a seed and its public key, in the
canonical envelope. The size comes from `sizeEd25519Envelope`, so the
key needs no check. Private: every caller passes the public key the
backend derived from `seed`, so the envelope always holds a matching
pair. -/
private def ofEd25519 (seed pub : Crypto.Key32) : PrivKey where
  keys := {
    keyType := .ed25519
    data := ed25519Envelope seed pub
    dataLt := by
      rw [sizeEd25519Envelope]
      simp [ed25519PrivBytes, ed25519SeedBytes, ed25519PubBytes, Varint.limit, Varint.maxBytes] }
  fits := by simp [privDataFits, sizeEd25519Envelope]

/-- The Ed25519 private key of a seed, with the public key the backend
derives from it. When `stored` is given, it must be that public key:
the spec defines the envelope as the seed and its public key. -/
private def ofSeed? (seed : Crypto.Key32) (stored : Option ByteArray) : Except Error PrivKey := do
  let pub ← (Crypto.ed25519PublicKey seed).mapError .crypto
  match stored with
  | some s => if s == pub.bytes then return ofEd25519 seed pub else throw .publicMismatch
  | none => return ofEd25519 seed pub

/-- An Ed25519 private key of any `Data` form owned contract 2 accepts,
as the canonical 64-byte envelope, so a marshal writes one form per
key. A stored public key must be the public key of the seed; go-libp2p
returns the stored half as the public key, so a mismatched envelope
would name another peer there.

| Input | Result |
|---|---|
| 32 bytes, the seed | the seed and its derived public key |
| 64 bytes, seed‖public | as given, the preferred form of the peer-ids spec |
| 96 bytes, seed‖public‖public | the first 64 bytes, when the two public copies match; otherwise the spec says to "reject or error out" |
-/
def ed25519OfData? (d : ByteArray) : Except Error PrivKey :=
  -- Each branch knows the size, so the seed is a `Key32` by proof.
  if h : d.size = ed25519SeedBytes then
    ofSeed? ⟨d, by simpa [ed25519SeedBytes] using h⟩ none
  else if h : d.size = ed25519PrivBytes then
    ofSeed? (Identity.ed25519Seed d h) (some (d.extract ed25519SeedBytes ed25519PrivBytes))
  else if h : d.size = ed25519LegacyPrivBytes then
    -- go compares the two copies in constant time. They are public
    -- data, so a plain comparison leaks nothing.
    if d.extract ed25519SeedBytes ed25519PrivBytes == d.extract ed25519PrivBytes d.size then
      ofSeed? ⟨d.extract 0 ed25519SeedBytes, by
          simp [ByteArray.size_extract, h, ed25519LegacyPrivBytes, ed25519PrivBytes,
            ed25519SeedBytes, ed25519PubBytes]⟩
        (some (d.extract ed25519SeedBytes ed25519PrivBytes))
    else .error .publicMismatch
  else .error (.keyData .ed25519 d.size)

/-- A DER private key in the form the table holds: the backend loads the
key and writes its type-specific DER, SEC1 for ECDSA and PKCS#1 for RSA.
The shell check runs first, so a `Data` that is not DER-shaped reports
`keyData`. ECDSA accepts a PKCS#8 import and holds its SEC1 form. RSA
accepts PKCS#1 only, so its `Data` must already be that form; go-libp2p
reads RSA with `x509.ParsePKCS1PrivateKey` and ECDSA with
`x509.ParseECPrivateKey`. -/
private def derOfKeys? (keys : Keys) (reencode : ByteArray → Except Crypto.CryptoError ByteArray)
    (importsOther : Bool) : Except Error PrivKey := do
  let _ ← ofHeld? keys
  let canonical ← (reencode keys.data).mapError .crypto
  if importsOther || canonical == keys.data then
    match Keys.ofData? keys.keyType canonical with
    | some held => ofHeld? held
    | none => throw (.keyData keys.keyType canonical.size)
  else throw (.keyData keys.keyType keys.data.size)

/-- The private key of a message: the strict per-type check, with each
`Data` brought to the one form the table holds, so a key marshals to one
form however it entered (owned contract 1). -/
def ofKeys? (keys : Keys) : Except Error PrivKey :=
  match keys.keyType with
  | .ed25519 => ed25519OfData? keys.data
  | .secp256k1 => ofHeld? keys
  | .ecdsa => derOfKeys? keys Crypto.p256Sec1 true
  | .rsa => derOfKeys? keys Crypto.rsaPkcs1 false

/-- The private key of a key type and its `Data` bytes. -/
def ofData? (t : KeyType) (d : ByteArray) : Except Error PrivKey :=
  match Keys.ofData? t d with
  | some keys => ofKeys? keys
  | none => .error (.keyData t d.size)

/-- The deterministic marshaling (owned contract 1): the message, `Type`
then `Data`, through the shared field table. -/
def marshal (k : PrivKey) : ByteArray := Pb.encodeFieldsB k.keys.toFields

/-- The public key of a private key. Ed25519 derives the point from the
seed; the constructors checked that the public half of the envelope is
that point. secp256k1 derives the
compressed point. ECDSA and RSA derive the SPKI DER, and the backend
rejects a DER key it cannot load. -/
def toPublic (k : PrivKey) : Except Error PubKey :=
  match h : k.keyType with
  | .ed25519 => do
    let pub ← (Crypto.ed25519PublicKey (k.ed25519Seed h)).mapError .crypto
    return PubKey.ofEd25519 pub
  | .secp256k1 => do
    PubKey.ofData? .secp256k1 (← (Crypto.secp256k1PublicKey (k.secp256k1Scalar h)).mapError .crypto)
  | .ecdsa => do
    PubKey.ofData? .ecdsa (← (Crypto.p256PublicKey k.data).mapError .crypto)
  | .rsa => do
    PubKey.ofData? .rsa (← (Crypto.rsaPublicKey k.data).mapError .crypto)

/-- Sign `msg` with the key, by the scheme of its type. Ed25519 and RSA
signatures are byte-identical on a re-sign. secp256k1 and ECDSA draw a
nonce, so two signatures differ, and both verify. -/
def sign (k : PrivKey) (msg : ByteArray) : ExceptT Error IO ByteArray :=
  match h : k.keyType with
  | .ed25519 => ExceptT.mk (pure ((Crypto.ed25519Sign (k.ed25519Seed h) msg).mapError .crypto))
  | .secp256k1 =>
    ExceptT.mk (pure ((Crypto.secp256k1Sign (k.secp256k1Scalar h) msg).mapError .crypto))
  | .ecdsa => (Crypto.p256Sign k.data msg).adapt .crypto
  | .rsa => ExceptT.mk (pure ((Crypto.rsaSign k.data msg).mapError .crypto))

end PrivKey

/-! ## The `ProtoMessage` instances

One instance per spec message, `PublicKey` and `PrivateKey`, over the
one shared field table (`Keys.toFields`, `Keys.ofFields?`). `ofFields?`
runs the strict per-type check, so the generic decoder
`Pb.decodeMessageB?` cannot build a key whose `Data` does not fit its
type. `Pb.Error` has no arm for a message-level rule, so a failed check
reports as `badField`; `PubKey.unmarshal?` and `PrivKey.unmarshal?` keep
the precise `Identity.Error`. -/

/-- An identity failure at the message boundary, as `Pb.Error`. -/
private def toPbError : Error → Pb.Error
  | .message e => e
  | _ => .badField

instance : Pb.ProtoMessage PubKey where
  toFields k := k.keys.toFields
  ofFields? fs := (Keys.ofFields? fs >>= PubKey.ofKeys?).mapError toPbError

instance : Pb.ProtoMessage PrivKey where
  toFields k := k.keys.toFields
  ofFields? fs := (Keys.ofFields? fs >>= PrivKey.ofKeys?).mapError toPbError

/-- A public key reads back from its own entries. -/
theorem PubKey.ofFieldsToFields (k : PubKey) :
    Pb.ProtoMessage.ofFields? (Pb.ProtoMessage.toFields k) = .ok k := by
  show (Keys.ofFields? k.keys.toFields >>= PubKey.ofKeys?).mapError toPbError = .ok k
  rw [Keys.ofFieldsToFields]
  simp [PubKey.ofKeys?, k.fits, bind, Except.bind, Except.mapError]

/-- A public key decodes back to itself over the byte model, with no
input left: the wire round trip of `codec/proto` (`Pb.decodeEncode`),
then the table's own. -/
theorem PubKey.decodeEncode (k : PubKey) :
    Pb.decodeMessage? (Pb.encodeMessage k) = .ok (k, []) := by
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.decodeEncode, bind, Except.bind,
    PubKey.ofFieldsToFields]

end Libp2p.Identity
