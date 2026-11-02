import Varint.UVarint
import Varint.Theorems

/-!
# Production `ByteArray` varint path (`encodeB`, `decodeB?`)

This module provides the `ByteArray` encoder and decoder used at the wire
boundary (ARCHITECTURE §4.2, §4.3, §6). `decodeB?` returns the decoded
`UVarint` and the number of bytes consumed so a framing caller knows
where its payload starts.

It imports `maxBytes` from `Varint/UVarint.lean` so the 9-byte budget has
a single canonical home (PRINCIPLES 1.5). Bridge theorems connect `encodeB`
and `decode?` through the `base/bytes` conversion axioms.
-/

set_option autoImplicit false

namespace Varint

open Varint.Mock

/-- Encode a `UVarint` into a `ByteArray`. -/
def encodeB (v : UVarint) : ByteArray :=
  ofNatList (encode v)

/-- Fuel-bounded `ByteArray` decoder reading from byte offset `i`.
Returns the decoded natural number and the count of consumed bytes. -/
def decodeBAtF : Nat → ByteArray → Nat → Except DecodeError (Nat × Nat)
  | 0, _, _ => .error .malformed
  | f + 1, b, i =>
    match b[i]? with
    | none => .error .truncated
    | some byte =>
      if byte.toNat < 128 then
        .ok (byte.toNat, 1)
      else
        match decodeBAtF f b (i + 1) with
        | .ok (v, c) =>
          if v = 0 then .error .malformed
          else .ok (128 * v + (byte.toNat - 128), c + 1)
        | .error e => .error e

/-- A value accepted by `decodeBAtF` with fuel `f` is strictly below `128 ^ f`. -/
theorem decodeBAtFLt : ∀ (f : Nat) (b : ByteArray) (i : Nat) (n : Nat) (c : Nat),
    decodeBAtF f b i = .ok (n, c) → n < 128 ^ f := by
  intro f
  induction f with
  | zero =>
    intro b i n c h
    simp [decodeBAtF] at h
  | succ f ih =>
    intro b i n c h
    rw [decodeBAtF] at h
    match hbi : b[i]? with
    | none =>
      simp [hbi] at h
    | some byte =>
      simp only [hbi] at h
      by_cases hb128 : byte.toNat < 128
      · simp only [hb128, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        have hpow : 1 ≤ 128 ^ f := Nat.one_le_pow f 128 (by decide)
        rw [Nat.pow_succ]
        omega
      · simp only [hb128, ↓reduceIte] at h
        match hf : decodeBAtF f b (i + 1) with
        | .error e =>
          simp [hf] at h
        | .ok (v, c') =>
          simp only [hf] at h
          by_cases hv : v = 0
          · simp [hv] at h
          · simp only [hv, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have hvlt : v < 128 ^ f := ih b (i + 1) v c' hf
            have hb256 : byte.toNat < 256 := UInt8.toNat_lt byte
            rw [Nat.pow_succ]
            omega

/-- A call accepted by `decodeBAtF` with fuel `f` consumes between 1 and `f` bytes. -/
theorem decodeBAtFConsumedBounds : ∀ (f : Nat) (b : ByteArray) (i : Nat) (n : Nat) (c : Nat),
    decodeBAtF f b i = .ok (n, c) → 1 ≤ c ∧ c ≤ f := by
  intro f
  induction f with
  | zero =>
    intro b i n c h
    simp [decodeBAtF] at h
  | succ f ih =>
    intro b i n c h
    rw [decodeBAtF] at h
    match hbi : b[i]? with
    | none =>
      simp [hbi] at h
    | some byte =>
      simp only [hbi] at h
      by_cases hb128 : byte.toNat < 128
      · simp only [hb128, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        omega
      · simp only [hb128, ↓reduceIte] at h
        match hf : decodeBAtF f b (i + 1) with
        | .error e =>
          simp [hf] at h
        | .ok (v, c') =>
          simp only [hf] at h
          by_cases hv : v = 0
          · simp [hv] at h
          · simp only [hv, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have hc := ih b (i + 1) v c' hf
            omega

/-- Decode a `UVarint` and its consumed byte count from `b` starting at byte offset `i`. -/
def decodeBAt? (b : ByteArray) (i : Nat) : Except DecodeError (UVarint × Nat) :=
  match h : decodeBAtF maxBytes b i with
  | .ok (n, c) =>
    have hlt : n < 128 ^ maxBytes := decodeBAtFLt maxBytes b i n c h
    have h63 : (128 : Nat) ^ maxBytes = 2 ^ 63 := rfl
    .ok (⟨n, h63 ▸ hlt⟩, c)
  | .error e => .error e

/-- Decode a `UVarint` and its consumed byte count from the start of `b`. -/
def decodeB? (b : ByteArray) : Except DecodeError (UVarint × Nat) :=
  decodeBAt? b 0

/-- Every successful `decodeB?` consumes between 1 and `maxBytes` (9) bytes. -/
theorem decodeBConsumedBounds {b : ByteArray} {v : UVarint} {c : Nat}
    (h : decodeB? b = .ok (v, c)) : 1 ≤ c ∧ c ≤ maxBytes := by
  unfold decodeB? decodeBAt? at h
  split at h
  · rename_i n c' hdec
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact decodeBAtFConsumedBounds maxBytes b 0 n c' hdec
  · simp at h

/-- Adapt `decodeB?` to return the unconsumed model tail so `checkModelPins`
compares the production decoder directly against `Codec.decode?`. -/
def decodeBModelAdapter (b : ByteArray) : Except DecodeError (UVarint × List Nat) :=
  match decodeB? b with
  | .ok (v, c) => .ok (v, (toNatList b).drop c)
  | .error e => .error e

/-- Converting `encodeB v` to the byte model yields `encode v`. -/
theorem toNatListEncodeB (v : UVarint) : toNatList (encodeB v) = encode v :=
  toNatListOfNatListOfLt (encode v) (encodeByteLt v)

/-- Decoding the byte model of `encodeB v` recovers `v` with no remainder. -/
theorem decodeToNatListEncodeB (v : UVarint) :
    decode? (toNatList (encodeB v)) = .ok (v, []) := by
  rw [toNatListEncodeB]
  exact decodeEncode v

/-- Rebuilding a `ByteArray` from the byte model of `encodeB v` yields `encodeB v`. -/
theorem ofNatListToNatListEncodeB (v : UVarint) :
    ofNatList (toNatList (encodeB v)) = encodeB v :=
  ofNatListToNatList (encodeB v)

/-- The generic round-trip harness succeeds on every list of `UVarint` samples. -/
theorem checkUVarintRoundTrips (samples : List UVarint) :
    checkRoundTrips samples = true :=
  checkRoundTripsEqTrue samples

end Varint
