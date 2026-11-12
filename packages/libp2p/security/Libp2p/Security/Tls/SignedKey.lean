import Libp2p.Security.Tls.Constants

/-!
# The `SignedKey` structure

The libp2p Public Key Extension carries one ASN.1 value (the TLS spec,
"libp2p Public Key Extension"):

```asn1
SignedKey ::= SEQUENCE {
  publicKey OCTET STRING,
  signature OCTET STRING
}
```

The value travels in DER (X.690), so each part is a tag byte, a
length, and the contents. This module holds the codec over the
`List Nat` byte model, with the round trip as a theorem (CLAUDE.md,
"Proofs and tests", rule 1). The production path calls the model
directly: a `SignedKey` is two short fields, read once per handshake,
so the `ByteArray` side converts at the edge and needs no second
decoder to pin.

## DER, the parts this module uses

* **Tags.** `0x30` is a SEQUENCE (constructed, universal 16), and
  `0x04` is an OCTET STRING (primitive, universal 4).
* **Lengths.** A length below 128 is one byte. A longer length is
  `0x80 + k`, then the value in `k` big-endian bytes. DER asks for the
  shortest form (X.690 §10.1), so `0x81` carries 128 to 255, and `0x82`
  carries 256 to 65535. The decoder refuses every other form: a long
  form for a short length, a leading zero byte, the indefinite form
  `0x80`, and more than two length bytes, which `maxDerLength` caps
  (root §5.1).
* **No trailing bytes.** The decoder refuses bytes after the SEQUENCE,
  and bytes after the second OCTET STRING inside it.

The decoder is stricter than go-libp2p's, which reads the value with
`asn1.Unmarshal` and drops the bytes after it
(`vendor/go-libp2p/p2p/security/tls/crypto.go`, line 191). Every
implementation writes the value with a DER encoder, so a valid peer
sends no trailing bytes, and the strict rule refuses no real
certificate (the package ARCHITECTURE, "Decisions").
-/

set_option autoImplicit false

namespace Libp2p.Security.Tls

/-! ## DER lengths and TLVs -/

/-- The SEQUENCE tag. -/
def tagSequence : Nat := 0x30

/-- The OCTET STRING tag. -/
def tagOctetString : Nat := 0x04

/-- The DER form of a length up to `maxDerLength`: the shortest form.
A larger length has no encoding here; the callers check the cap
first. -/
def encodeLength (n : Nat) : List Nat :=
  if n < 128 then [n]
  else if n < 256 then [0x81, n]
  else [0x82, n / 256, n % 256]

/-- Read a DER length: the value and the bytes after it. `none` for
every form that is not the shortest, and for more than two length
bytes. -/
def decodeLength : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: rest =>
    if b < 128 then some (b, rest)
    else if b = 0x81 then
      match rest with
      | x :: r => if 128 ≤ x ∧ x < 256 then some (x, r) else none
      | [] => none
    else if b = 0x82 then
      match rest with
      -- A first byte of 0 would be a leading zero, the long way to
      -- write a length below 256.
      | h :: l :: r => if 1 ≤ h ∧ h < 256 ∧ l < 256 then some (h * 256 + l, r) else none
      | _ => none
    else none

/-- Every length up to the cap reads back, whatever follows it. -/
theorem decodeLength_encodeLength {n : Nat} (h : n ≤ maxDerLength) (rest : List Nat) :
    decodeLength (encodeLength n ++ rest) = some (n, rest) := by
  unfold maxDerLength at h
  unfold encodeLength
  by_cases h1 : n < 128
  · simp [decodeLength, h1]
  · by_cases h2 : n < 256
    · simp [decodeLength, h1, h2]
    · simp only [h1, h2, ite_false, List.cons_append, decodeLength]
      have hh : 1 ≤ n / 256 ∧ n / 256 < 256 ∧ n % 256 < 256 := by omega
      simp [hh]
      omega

/-- One TLV: the tag, the DER length, the contents. -/
def encodeTlv (tag : Nat) (contents : List Nat) : List Nat :=
  tag :: encodeLength contents.length ++ contents

/-- Read one TLV with the tag `tag`: its contents and the bytes after
it. `none` for another tag, a bad length, or a length past the end of
the input. -/
def decodeTlv (tag : Nat) : List Nat → Option (List Nat × List Nat)
  | [] => none
  | t :: rest =>
    if t = tag then
      match decodeLength rest with
      | some (n, r) => if n ≤ r.length then some (r.take n, r.drop n) else none
      | none => none
    else none

/-- A TLV whose contents fit the cap reads back, whatever follows
it. -/
theorem decodeTlv_encodeTlv (tag : Nat) {c : List Nat} (h : c.length ≤ maxDerLength)
    (rest : List Nat) : decodeTlv tag (encodeTlv tag c ++ rest) = some (c, rest) := by
  simp [encodeTlv, decodeTlv, List.append_assoc, decodeLength_encodeLength h]

/-! ## The structure -/

/-- The value of the extension: the marshaled `PublicKey` protobuf of
the host key, and the host key's signature over the prefix and the
certificate's SubjectPublicKeyInfo. -/
structure SignedKey where
  /-- The host public key, as the `PublicKey` protobuf of the peer-id
  spec. -/
  publicKey : List Nat
  /-- The signature over `signaturePrefix ++ spki`. -/
  signature : List Nat
  deriving DecidableEq, Repr

namespace SignedKey

/-- The contents of the SEQUENCE: the two OCTET STRINGs. -/
def body (sk : SignedKey) : List Nat :=
  encodeTlv tagOctetString sk.publicKey ++ encodeTlv tagOctetString sk.signature

/-- The fields and the SEQUENCE fit the cap, so every length has its
two-byte form. -/
def Fits (sk : SignedKey) : Prop :=
  sk.publicKey.length ≤ maxDerLength ∧ sk.signature.length ≤ maxDerLength ∧
    sk.body.length ≤ maxDerLength

instance (sk : SignedKey) : Decidable sk.Fits := by
  unfold Fits
  exact inferInstance

/-- The DER encoding. -/
def encode (sk : SignedKey) : List Nat := encodeTlv tagSequence sk.body

/-- The DER encoding, when the value fits the cap. -/
def encode? (sk : SignedKey) : Option (List Nat) :=
  if sk.Fits then some sk.encode else none

/-- Read a `SignedKey`: one SEQUENCE of two OCTET STRINGs, with no
byte after either. -/
def decode? (bs : List Nat) : Option SignedKey :=
  match decodeTlv tagSequence bs with
  | some (body, []) =>
    match decodeTlv tagOctetString body with
    | some (pk, r) =>
      match decodeTlv tagOctetString r with
      | some (sig, []) => some ⟨pk, sig⟩
      | _ => none
    | none => none
  | _ => none

/-- The round trip: a value that fits reads back from its encoding. -/
theorem decode_encode (sk : SignedKey) (h : sk.Fits) : decode? sk.encode = some sk := by
  obtain ⟨hpk, hsig, hbody⟩ := h
  have outer := decodeTlv_encodeTlv tagSequence hbody []
  have first := decodeTlv_encodeTlv tagOctetString hpk (encodeTlv tagOctetString sk.signature)
  have second := decodeTlv_encodeTlv tagOctetString hsig []
  simp only [List.append_nil] at outer second
  -- The outer TLV reads back first; its match then reduces to the body.
  unfold decode? encode
  rw [outer]
  dsimp only
  unfold body
  rw [first]
  dsimp only
  rw [second]

/-- `encode?` answers exactly when the value fits, and its answer
reads back. -/
theorem decode_encode? {sk : SignedKey} {bs : List Nat} (h : sk.encode? = some bs) :
    decode? bs = some sk := by
  unfold encode? at h
  split at h
  · cases h
    exact decode_encode sk (by assumption)
  · cases h

end SignedKey

/-- A SEQUENCE that holds one empty OCTET STRING only is no
`SignedKey`. -/
example : SignedKey.decode? [0x30, 0x02, 0x04, 0x00] = none := by decide

/-- A long-form length for a short value is refused. -/
example : decodeLength [0x81, 0x05] = none := by decide

/-- The empty `SignedKey`: two empty OCTET STRINGs in a SEQUENCE. -/
example : (SignedKey.mk [] []).encode = [0x30, 0x04, 0x04, 0x00, 0x04, 0x00] := by decide

end Libp2p.Security.Tls
