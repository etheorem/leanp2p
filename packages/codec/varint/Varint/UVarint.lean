import Varint.Mock

/-!
# Unsigned varint core (`UVarint`, `encode`, `decode?`)

This module implements the unsigned varint (LEB128) of the multiformats
specification (ARCHITECTURE §3.2, §3.7, §4.3, §5.1). Each byte carries
seven value bits in its low seven positions, and the high bit marks a
continuation byte. The first byte holds the least significant group.

The specification enforces two bounds:
1. Encodings are minimal, so a trailing zero group after a continuation
   byte is rejected as `malformed`.
2. An encoding spans at most 9 bytes (63 bits). A prefix that reaches
   the 9-byte budget without a terminator byte is rejected as
   `malformed` so a reader stops waiting at the boundary.

`UVarint` is a proof-carrying newtype that witnesses `val < 2 ^ 63`.
Because the type carries the budget invariant, `Codec UVarint` satisfies
the unconditional `LawfulCodec UVarint` round-trip and inverse laws.
-/

set_option autoImplicit false

namespace Varint

open Varint.Mock

/-- Maximum encoded length in bytes for a multiformats unsigned varint. -/
def maxBytes : Nat := 9

/-- Maximum bit width of a multiformats unsigned varint. -/
def maxBits : Nat := 63

/-- Exclusive upper bound (`2 ^ 63`) on the value of a multiformats unsigned varint. -/
def maxVal : Nat := 2 ^ 63

/-- Proof-carrying unsigned varint value bounded below `2 ^ 63` (ARCHITECTURE §3.7). -/
structure UVarint where
  /-- The underlying natural number. -/
  val : Nat
  /-- Proof that the value fits within the 63-bit multiformats budget. -/
  isLt : val < 2 ^ 63
  deriving Repr, DecidableEq, BEq

/-- Two `UVarint` values with equal numeric payloads are equal. -/
theorem UVarint.ext {a b : UVarint} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- The zero `UVarint`. -/
def UVarint.zero : UVarint := ⟨0, by decide⟩

instance : Inhabited UVarint := ⟨UVarint.zero⟩

/-- Construct a `UVarint` after checking the 63-bit bound at the boundary.
Returns `none` only when `n` is at least `2 ^ 63`. -/
def UVarint.ofNat? (n : Nat) : Option UVarint :=
  if h : n < 2 ^ 63 then some ⟨n, h⟩ else none

/-- `UVarint.ofNat?` succeeds whenever `n < 2 ^ 63`. -/
theorem UVarint.ofNat?EqSome {n : Nat} (h : n < 2 ^ 63) :
    UVarint.ofNat? n = some ⟨n, h⟩ := by
  simp [UVarint.ofNat?, h]

/-- `UVarint.ofNat?` returns `none` whenever `2 ^ 63 ≤ n`. -/
theorem UVarint.ofNat?EqNone {n : Nat} (h : 2 ^ 63 ≤ n) :
    UVarint.ofNat? n = none := by
  have hnot : ¬ (n < 2 ^ 63) := by omega
  simp [UVarint.ofNat?, hnot]

/-- Re-wrapping the value of an existing `UVarint` recovers that `UVarint`. -/
theorem UVarint.ofNat?Val (v : UVarint) : UVarint.ofNat? v.val = some v := by
  cases v with
  | mk val isLt =>
    exact UVarint.ofNat?EqSome isLt

/-- Encode a natural number into its minimal LEB128 byte list. -/
def encodeNat (n : Nat) : List Nat :=
  if n < 128 then [n] else (n % 128 + 128) :: encodeNat (n / 128)
termination_by n
decreasing_by omega

/-- Values below 128 encode to a single terminator byte. -/
theorem encodeNatSmall {n : Nat} (h : n < 128) : encodeNat n = [n] := by
  rw [encodeNat]
  simp [h]

/-- Values of at least 128 emit a continuation byte followed by the encoding of `n / 128`. -/
theorem encodeNatBig {n : Nat} (h : 128 ≤ n) :
    encodeNat n = (n % 128 + 128) :: encodeNat (n / 128) := by
  have hnot : ¬ (n < 128) := by omega
  rw [encodeNat]
  simp [hnot]

/-- Encode a `UVarint` over the `List Nat` byte model. -/
def encode (v : UVarint) : List Nat :=
  encodeNat v.val

/-- Fuel-bounded LEB128 decoder over the `List Nat` byte model.
Exhausting the fuel `f` reports `malformed`. Reaching the end of the
input while fuel remains reports `truncated`. A byte of 256 or more, or
a recursive value of zero after a continuation byte, reports `malformed`. -/
def decodeF : Nat → List Nat → Except DecodeError (Nat × List Nat)
  | 0, _ => .error .malformed
  | _ + 1, [] => .error .truncated
  | f + 1, b :: bs =>
    if b < 128 then
      .ok (b, bs)
    else if b < 256 then
      match decodeF f bs with
      | .ok (v, bs') =>
        if v = 0 then .error .malformed
        else .ok (128 * v + (b - 128), bs')
      | .error e => .error e
    else
      .error .malformed

/-- A value accepted with fuel `f` is strictly bounded by `128 ^ f`. -/
theorem decodeFLt : ∀ (f : Nat) (bs : List Nat) (n : Nat) (rest : List Nat),
    decodeF f bs = .ok (n, rest) → n < 128 ^ f := by
  intro f
  induction f with
  | zero =>
    intro bs n rest h
    simp [decodeF] at h
  | succ f ih =>
    intro bs n rest h
    match bs with
    | [] => simp [decodeF] at h
    | b :: bs' =>
      simp only [decodeF] at h
      by_cases hb128 : b < 128
      · simp only [hb128, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        have hpow : 1 ≤ 128 ^ f := Nat.one_le_pow f 128 (by decide)
        rw [Nat.pow_succ]
        omega
      · by_cases hb256 : b < 256
        · simp only [hb128, hb256, ↓reduceIte] at h
          match hf : decodeF f bs' with
          | .error e =>
            simp [hf] at h
          | .ok (v, bs'') =>
            simp only [hf] at h
            by_cases hv : v = 0
            · simp [hv] at h
            · simp only [hv, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, _⟩ := h
              have hvlt : v < 128 ^ f := ih bs' v bs'' hf
              rw [Nat.pow_succ]
              omega
        · simp [hb128, hb256] at h

/-- Decode a `UVarint` and the unconsumed tail from the `List Nat` byte model.
Enforces minimal encodings and the 9-byte (63-bit) budget. -/
def decode? (bs : List Nat) : Except DecodeError (UVarint × List Nat) :=
  match h : decodeF maxBytes bs with
  | .ok (n, rest) =>
    have hlt : n < 128 ^ maxBytes := decodeFLt maxBytes bs n rest h
    have h63 : (128 : Nat) ^ maxBytes = 2 ^ 63 := rfl
    .ok (⟨n, h63 ▸ hlt⟩, rest)
  | .error e => .error e

/-- Any natural number below `128 ^ (k + 1)` encodes in at most `k + 1` bytes. -/
theorem encodeNatLengthLePow : ∀ (k : Nat) (n : Nat),
    n < 128 ^ (k + 1) → (encodeNat n).length ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have hn128 : n < 128 := by
      simpa using hn
    rw [encodeNatSmall hn128]
    simp
  | succ k ih =>
    intro n hn
    rw [Nat.pow_succ] at hn
    by_cases hb : n < 128
    · rw [encodeNatSmall hb]
      simp
    · have h128le : 128 ≤ n := by omega
      have hrec : n / 128 < 128 ^ (k + 1) :=
        (Nat.div_lt_iff_lt_mul (by decide)).mpr hn
      have hih := ih (n / 128) hrec
      rw [encodeNatBig h128le]
      simp
      omega

/-- Decoding `encodeNat n ++ rest` with sufficient fuel `f` returns `(n, rest)`. -/
theorem decodeFEncodeNatAppend : ∀ (n : Nat) (rest : List Nat),
    ∀ (f : Nat), (encodeNat n).length ≤ f →
    decodeF f (encodeNat n ++ rest) = .ok (n, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro rest f hf
    by_cases h : n < 128
    · match f with
      | 0 =>
        rw [encodeNatSmall h] at hf
        simp at hf
      | f' + 1 =>
        rw [encodeNatSmall h, List.cons_append, decodeF]
        simp [h]
    · have h128 : 128 ≤ n := by omega
      match f with
      | 0 =>
        rw [encodeNatBig h128] at hf
        simp at hf
      | f' + 1 =>
        have hlt : n / 128 < n := by omega
        have hlen : (encodeNat (n / 128)).length ≤ f' := by
          have hlen' : (encodeNat n).length = (encodeNat (n / 128)).length + 1 := by
            rw [encodeNatBig h128]
            simp
          omega
        have hnot128 : ¬ (n % 128 + 128 < 128) := by omega
        have hlt256 : n % 128 + 128 < 256 := by omega
        have hdiv0 : ¬ (n / 128 = 0) := by omega
        have hrec := ih (n / 128) hlt rest f' hlen
        have hval : 128 * (n / 128) + (n % 128 + 128 - 128) = n := by omega
        rw [encodeNatBig h128, List.cons_append, decodeF]
        simp only [hnot128, hlt256, ↓reduceIte, hrec, hdiv0, hval]

/-- Every input accepted by `decodeF` begins with the minimal encoding of the decoded number. -/
theorem decodeFEncodeNatInv : ∀ (f : Nat) (n : Nat) (rest : List Nat) (bs : List Nat),
    decodeF f bs = .ok (n, rest) → encodeNat n ++ rest = bs := by
  intro f
  induction f with
  | zero =>
    intro n rest bs h
    simp [decodeF] at h
  | succ f ih =>
    intro n rest bs h
    match bs with
    | [] => simp [decodeF] at h
    | b :: bs' =>
      simp only [decodeF] at h
      by_cases hb128 : b < 128
      · simp only [hb128, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [encodeNatSmall hb128]
        rfl
      · by_cases hb256 : b < 256
        · simp only [hb128, hb256, ↓reduceIte] at h
          match hf : decodeF f bs' with
          | .error e =>
            simp [hf] at h
          | .ok (v, bs'') =>
            simp only [hf] at h
            by_cases hv : v = 0
            · simp [hv] at h
            · simp only [hv, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hn, hrest⟩ := h
              have hbs : encodeNat v ++ bs'' = bs' := ih v bs'' bs' hf
              have hge : 128 ≤ n := by omega
              rw [encodeNatBig hge, List.cons_append,
                  show n % 128 + 128 = b from by omega,
                  show n / 128 = v from by omega,
                  ← hrest, hbs]
        · simp [hb128, hb256] at h

/-- Round-trip law for `UVarint`: decoding `encode v` returns `(v, [])`. -/
theorem decodeEncode (v : UVarint) :
    decode? (encode v) = .ok (v, []) := by
  unfold decode?
  have h128 : (2 : Nat) ^ 63 = 128 ^ 9 := rfl
  have hv : v.val < 128 ^ (8 + 1) := by
    rw [← h128]
    exact v.isLt
  have hle : (encode v).length ≤ maxBytes :=
    encodeNatLengthLePow 8 v.val hv
  have hdec : decodeF maxBytes (encode v) = .ok (v.val, []) := by
    have happ := decodeFEncodeNatAppend v.val [] maxBytes hle
    simpa [encode] using happ
  split
  · rename_i n rest' h
    rw [hdec] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rename_i e h
    rw [hdec] at h
    simp at h

/-- Inverse law for `UVarint`: every accepted input splits into `encode v ++ rest`. -/
theorem encodeDecode (bs : List Nat) (v : UVarint) (rest : List Nat)
    (h : decode? bs = .ok (v, rest)) : encode v ++ rest = bs := by
  unfold decode? at h
  split at h
  · rename_i n rest' hdec
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact decodeFEncodeNatInv maxBytes n rest' bs hdec
  · simp at h

instance : Codec UVarint where
  encode := encode
  decode? := decode?

instance : LawfulCodec UVarint where
  decode_encode := decodeEncode
  encode_decode := encodeDecode

end Varint
