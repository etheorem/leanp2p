import Multiformats.Tables
import Multiformats.Constants
import Multiformats.Wire

/-!
# Strict multihash framing

The function code and digest length are minimal varints. Digests are
opaque bytes; computing a digest belongs to the caller. A standalone
decode rejects trailing bytes, while the prefix form composes with CID.
-/

set_option autoImplicit false

namespace Multiformats

/-- A registered algorithm and a bounded byte-valued digest. -/
structure Multihash where
  code : HashCode
  digest : List Nat
  valid : ∀ b ∈ digest, b < 256
  bounded : digest.length ≤ maxDigestBytes
  deriving DecidableEq, Repr

namespace Multihash

open Mock

/-- Raw digest data is checked once when it enters the wire model. -/
def ofDigest? (code : HashCode) (digest : List Nat) : Except Error Multihash :=
  if h : (∀ b ∈ digest, b < 256) ∧ digest.length ≤ maxDigestBytes then
    .ok ⟨code, digest, h.1, h.2⟩
  else .error .badDigest

/-- The digest bound is far below the shared integer budget. -/
theorem digestLengthLt (value : Multihash) : value.digest.length < Varint.limit := by
  have h := value.bounded
  simp only [maxDigestBytes] at h
  simp only [Varint.limit]
  omega

/-- The declared length is derived from the digest, so it cannot disagree. -/
def encode (value : Multihash) : List Nat :=
  Wire.encodeNat value.code.toCode ++ Wire.encodeNat value.digest.length ++ value.digest

/-- A prefix parser constructs the validity proofs before returning a value. -/
def decodeAt? (input : List Nat) : Except Error (Multihash × List Nat) := do
  let (rawCode, tail) ← (Varint.decode? input).mapError Error.framing
  let code ← match HashCode.ofCode? rawCode.val with
    | none => .error .unknownHash
    | some code => .ok code
  if code.toCode = rawCode.val then
    let (length, tail) ← (Varint.decode? tail).mapError Error.framing
    let (payload, rest) ← Wire.takeBytes maxDigestBytes length.val tail
    if h : (∀ b ∈ payload, b < 256) ∧ payload.length ≤ maxDigestBytes then
      .ok (⟨code, payload, h.1, h.2⟩, rest)
    else .error .badDigest
  else .error .unknownHash

/-- Standalone messages reject any bytes after the declared digest. -/
def decode? (input : List Nat) : Except Error (Multihash × List Nat) := do
  let (value, rest) ← decodeAt? input
  if rest = [] then .ok (value, []) else .error .badDigest

/-- Bounded values round-trip with any suffix untouched. -/
theorem decodeAtEncode (value : Multihash) (rest : List Nat) :
    decodeAt? (encode value ++ rest) = .ok (value, rest) := by
  have hc : value.code.toCode < Varint.limit := HashCode.codeLt value.code
  have hl := digestLengthLt value
  have ht := Wire.takeBytesAppend maxDigestBytes value.digest rest value.bounded value.valid
  simp [decodeAt?, encode, Wire.encodeNat, Wire.toVarint, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hl, List.append_assoc, Varint.decodeEncodeSuffix,
    HashCode.ofCodeToCode, ht, value.bounded, and_true,
    Bind.bind, Except.bind, Except.mapError]
  split
  · rfl
  · rename_i invalid
    exact (invalid value.valid).elim

/-- The standalone codec has an unconditional roundtrip. -/
theorem decodeEncode (value : Multihash) : decode? (encode value) = .ok (value, []) := by
  have h := decodeAtEncode value []
  simp only [List.append_nil] at h
  simp [decode?, h, Bind.bind, Except.bind]

/-- Successful prefix parsing accounts for every consumed byte. -/
theorem decodeAtOk (input : List Nat) (value : Multihash) (rest : List Nat)
    (h : decodeAt? input = .ok (value, rest)) : input = encode value ++ rest := by
  cases hr : Varint.decode? input with
  | error error => simp [decodeAt?, hr, Except.mapError, Bind.bind, Except.bind] at h
  | ok pair =>
      obtain ⟨raw, tail⟩ := pair
      simp only [decodeAt?, hr, Except.mapError, Bind.bind, Except.bind] at h
      cases hc : HashCode.ofCode? raw.val with
      | none => simp [hc] at h
      | some code =>
          simp only [hc] at h
          split at h
          · rename_i codeEq
            cases hl : Varint.decode? tail with
            | error error => simp [hl] at h
            | ok pair =>
                obtain ⟨length, afterLength⟩ := pair
                simp only [hl] at h
                cases hp : Wire.takeBytes maxDigestBytes length.val afterLength with
                | error error => simp [hp] at h
                | ok pair =>
                    obtain ⟨payload, after⟩ := pair
                    simp only [hp] at h
                    split at h
                    · have he := Prod.mk.inj (Except.ok.inj h)
                      rcases he with ⟨rfl, rfl⟩
                      obtain ⟨hlen, _, _, hsplit⟩ :=
                        Wire.takeBytesOk maxDigestBytes length.val afterLength payload after hp
                      have hraw := Varint.encodeDecode input raw tail hr
                      have hlength := Varint.encodeDecode tail length afterLength hl
                      have hall := hraw.trans (congrArg (Varint.encode raw ++ ·)
                        (hlength.trans (congrArg (Varint.encode length ++ ·) hsplit)))
                      simpa only [encode, Wire.encodeNat, codeEq, hlen, Wire.toVarintVal,
                        List.append_assoc] using hall
                    · cases h
          · cases h

/-- The standalone inverse rejects trailing bytes before proving exact re-encoding. -/
theorem encodeDecode (input : List Nat) (value : Multihash) (rest : List Nat)
    (h : decode? input = .ok (value, rest)) : input = encode value ++ rest := by
  cases hd : decodeAt? input with
  | error error => simp [decode?, hd, Bind.bind, Except.bind] at h
  | ok pair =>
      obtain ⟨parsed, tail⟩ := pair
      simp only [decode?, hd, Bind.bind, Except.bind] at h
      split at h
      · rename_i empty
        subst tail
        have he := Prod.mk.inj (Except.ok.inj h)
        rcases he with ⟨rfl, rfl⟩
        exact decodeAtOk input parsed [] hd
      · cases h

/-- The detailed parser error is mapped once at the shared codec boundary. -/
instance : Bytes.Codec Multihash where
  encode := encode
  decode? input := (decode? input).mapError Error.toDecodeError

/-- The instance uses the two proved multihash laws, with the dependency's orientation. -/
instance : Bytes.LawfulCodec Multihash where
  decodeEncode value := by
    change (decode? (encode value)).mapError Error.toDecodeError = _
    rw [decodeEncode]
    rfl
  encodeDecode input value rest h := by
    change (decode? input).mapError Error.toDecodeError = .ok (value, rest) at h
    cases hd : decode? input with
    | error error => simp [hd, Except.mapError] at h
    | ok pair =>
        simp only [hd, Except.mapError, Except.ok.injEq] at h
        cases h
        exact (encodeDecode input value rest hd).symm

/-- The wire representation distinguishes every valid multihash value. -/
theorem encodeInjective {a b : Multihash} (h : encode a = encode b) : a = b := by
  have left := decodeEncode a
  rw [h, decodeEncode b] at left
  exact (Prod.mk.inj (Except.ok.inj left)).1.symm

/-- No conversion to ByteArray changes an encoded model entry. -/
theorem encodeBytes (value : Multihash) : ∀ b ∈ encode value, b < 256 := by
  intro b hb
  simp only [encode, List.mem_append] at hb
  rcases hb with (hb | hb) | hb
  · exact Varint.encodeBytes (Wire.toVarint value.code.toCode) b hb
  · exact Varint.encodeBytes (Wire.toVarint value.digest.length) b hb
  · exact value.valid b hb

/-- A production cursor parser checks the cap before allocating the payload. -/
def decodeAtB? (input : ByteArray) (position : Nat := 0) : Except Error (Multihash × Nat) := do
  let (rawCode, next) ← Wire.readVarintAt input position
  let code ← match HashCode.ofCode? rawCode.val with
    | none => .error .unknownHash
    | some code => .ok code
  let (length, next) ← Wire.readVarintAt input next
  let (payload, after) ← Wire.takeBytesAt input next length.val maxDigestBytes
  let value ← ofDigest? code payload
  .ok (value, after)

/-- The byte boundary has the same standalone trailing-byte rule as the model. -/
def ofByteArray? (input : ByteArray) : Except Error Multihash := do
  let (value, used) ← decodeAtB? input
  if used = input.size then .ok value else .error .badDigest

/-- A caller can append a digest without building an intermediate encoded list. -/
def appendB (value : Multihash) (output : ByteArray) : ByteArray :=
  let output := Wire.writeNatB value.code.toCode output
  let output := Wire.writeNatB value.digest.length output
  Wire.writeBytesB value.digest output

/-- The production encoder writes directly into its byte builder. -/
def toByteArray (value : Multihash) : ByteArray := appendB value ByteArray.empty

end Multihash

end Multiformats
