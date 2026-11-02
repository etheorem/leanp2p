import Varint.UVarint

/-!
# Unsigned varint theorems

This module proves the model properties beyond the `LawfulCodec UVarint`
instance law (ARCHITECTURE §4.3, §6):

- `encodeLengthLe`: the encoding of a `UVarint` takes at most 9 bytes.
- `decodeEncodeAppend`: decoding `encode v ++ rest` returns `(v, rest)`.
- `decodeEncodeInv`: a successful decode splits the input into
  `encode v ++ rest` without any side condition on the input bytes.
- Byte-range and length bounds for encoded values, injectivity of
  `encode`, and concrete rejection theorems for non-minimal, over-long,
  and truncated inputs.
-/

set_option autoImplicit false

namespace Varint

open Varint.Mock

/-- Budget lemma: every `UVarint` encodes in at most `maxBytes` (9) bytes. -/
theorem encodeLengthLe (v : UVarint) : (encode v).length ≤ maxBytes := by
  have h128 : (2 : Nat) ^ 63 = 128 ^ 9 := rfl
  have hv : v.val < 128 ^ (8 + 1) := by
    rw [← h128]
    exact v.isLt
  exact encodeNatLengthLePow 8 v.val hv

/-- `encodeNat` never produces the empty list. -/
theorem encodeNatNonempty (n : Nat) : encodeNat n ≠ [] := by
  by_cases h : n < 128
  · rw [encodeNatSmall h]
    simp
  · have h128 : 128 ≤ n := by omega
    rw [encodeNatBig h128]
    simp

/-- Every `UVarint` encoding is non-empty. -/
theorem encodeNonempty (v : UVarint) : encode v ≠ [] :=
  encodeNatNonempty v.val

/-- Every `UVarint` encoding has positive byte length. -/
theorem encodeLengthPos (v : UVarint) : 0 < (encode v).length := by
  have hne := encodeNonempty v
  cases h : encode v with
  | nil => exact absurd h hne
  | cons _ _ => simp

/-- Every byte produced by `encodeNat` is strictly less than 256. -/
theorem encodeNatByteLt : ∀ (n : Nat) (b : Nat), b ∈ encodeNat n → b < 256 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro b hb
    by_cases h : n < 128
    · rw [encodeNatSmall h] at hb
      simp only [List.mem_singleton] at hb
      omega
    · have h128 : 128 ≤ n := by omega
      rw [encodeNatBig h128, List.mem_cons] at hb
      cases hb with
      | inl hhead =>
        omega
      | inr htail =>
        exact ih (n / 128) (by omega) b htail

/-- Every byte in `encode v` is a valid byte value below 256. -/
theorem encodeByteLt (v : UVarint) : ∀ b ∈ encode v, b < 256 :=
  encodeNatByteLt v.val

/-- Suffix round-trip theorem: decoding `encode v ++ rest` returns `(v, rest)`. -/
theorem decodeEncodeAppend (v : UVarint) (rest : List Nat) :
    decode? (encode v ++ rest) = .ok (v, rest) := by
  unfold decode?
  have hdec : decodeF maxBytes (encode v ++ rest) = .ok (v.val, rest) :=
    decodeFEncodeNatAppend v.val rest maxBytes (encodeLengthLe v)
  split
  · rename_i n rest' h
    rw [hdec] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rename_i e h
    rw [hdec] at h
    simp at h

/-- Accepted-input split: if `decode? bs = .ok (v, rest)`, then `bs = encode v ++ rest`.
Requires no side condition on `bs` because `decode?` rejects entries of 256 or more. -/
theorem decodeEncodeInv {bs : List Nat} {v : UVarint} {rest : List Nat}
    (h : decode? bs = .ok (v, rest)) : bs = encode v ++ rest :=
  (encodeDecode bs v rest h).symm

/-- The input length of an accepted decode equals the encoded length plus the remainder length. -/
theorem decodeConsumedLength {bs : List Nat} {v : UVarint} {rest : List Nat}
    (h : decode? bs = .ok (v, rest)) : bs.length = (encode v).length + rest.length := by
  rw [decodeEncodeInv h, List.length_append]

/-- A successful decode consumes at most `maxBytes` (9) bytes from the input. -/
theorem decodeConsumedLeMaxBytes {bs : List Nat} {v : UVarint} {rest : List Nat}
    (h : decode? bs = .ok (v, rest)) : bs.length - rest.length ≤ maxBytes := by
  have hlen := decodeConsumedLength h
  have hle := encodeLengthLe v
  omega

/-- `encode` is injective on `UVarint`. -/
theorem encodeInjective {a b : UVarint} (h : encode a = encode b) : a = b := by
  have ha := decodeEncode a
  rw [h, decodeEncode b] at ha
  simp only [Except.ok.injEq, Prod.mk.injEq] at ha
  exact ha.1.symm

/-- Non-minimal encoding `0x80 0x00` for zero is rejected as `malformed`. -/
theorem decodeNonminimalZero : decode? [0x80, 0x00] = .error .malformed := rfl

/-- Non-minimal encoding `0x81 0x00` for one is rejected as `malformed`. -/
theorem decodeNonminimalOne : decode? [0x81, 0x00] = .error .malformed := rfl

/-- A 10-byte prefix (nine continuation bytes and one terminator) is rejected as `malformed`. -/
theorem decodeTooLong : decode? (List.replicate 9 0xff ++ [0x01]) = .error .malformed := rfl

/-- Nine continuation bytes exhaust the 9-byte budget and are rejected as `malformed`. -/
theorem decodeNineContinuations : decode? (List.replicate 9 0x80) = .error .malformed := rfl

/-- An empty byte list is reported as `truncated`. -/
theorem decodeTruncatedEmpty : decode? [] = .error .truncated := rfl

/-- A single continuation byte `0x80` is reported as `truncated`. -/
theorem decodeTruncatedSingle : decode? [0x80] = .error .truncated := rfl

/-- An out-of-range model entry (`256`) is rejected as `malformed`. -/
theorem decodeByteGe256 : decode? [256] = .error .malformed := rfl

end Varint
