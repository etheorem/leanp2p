import Varint.Mock.Bytes

/-!
# The unsigned varint

The unsigned varint of the multiformats spec
(`vendor/unsigned-varint/README.md`). Each byte carries 7 bits of
the value, least significant group first. The high bit of a byte marks
a continuation: `1` means another byte follows, `0` ends the value.
Examples from the spec: 1 is `0x01`, 127 is `0x7F`, 128 is
`0x80 0x01`, 300 is `0xAC 0x02`.

The spec adds two rules, and both are protocol rules here
(ARCHITECTURE §4.3):

* **Minimal.** A value takes the fewest bytes possible. A final group of
  zero after a continuation byte is the non-minimal case: `0x80 0x00`
  for zero, `0x81 0x00` for one.
* **At most 9 bytes.** Nine bytes carry 63 bits. A ninth byte that is
  still a continuation spends the budget, and no later byte can complete
  the value, so the decoder answers `malformed` at once. A hostile peer
  cannot turn its length field into our unbounded wait (PRINCIPLES 2.3).

An input that ends while a within-budget varint is still open answers
`truncated`: more bytes may complete it (`base/bytes`, `DecodeError`).

This module holds the newtype, the model core over `List Nat`, and the
`Codec` and `LawfulCodec` instances with the proof of the law. The
instances live with the type (ARCHITECTURE §3.2).
-/

set_option autoImplicit false

namespace Varint

open Varint.Mock.Bytes

/-- The byte budget of a varint: at most 9 bytes. Every other module
takes the budget from here (PRINCIPLES 1.5). -/
def maxBytes : Nat := 9

/-- The first value outside the budget: 9 bytes of 7 bits carry the
values below `2 ^ 63`. -/
def limit : Nat := 2 ^ (7 * maxBytes)

/-- A varint value: a `Nat` inside the 63 bits that 9 bytes carry. The
proof field is the budget fact of §3.7. A decoder checks it once where
the bytes enter, and a core that takes a `UVarint` never checks the
size again. Lean erases the proof at run time. -/
structure UVarint where
  /-- The value. -/
  val : Nat
  /-- The value fits the 9-byte budget. -/
  isLt : val < limit
  deriving DecidableEq, Repr

/-! ## The model core -/

/-- The encoding of a `Nat`: a continuation byte per 7-bit group while
more than 7 bits remain, then the final group. The recursion divides by
128, so `termination_by` names `n` and `omega` closes the step. -/
def encodeNat (n : Nat) : List Nat :=
  if n < 128 then [n] else (n % 128 + 128) :: encodeNat (n / 128)
termination_by n
decreasing_by omega

/-- The encoding of a varint over the byte model. -/
def encode (v : UVarint) : List Nat :=
  encodeNat v.val

/-- The groups from byte `i` on, with the rest of the input. `i` counts
the bytes read before this one, so `i = 0` is the first byte. It decides
the minimal rule (a zero terminator only as the first byte) and the
budget (the byte at `i = 8` must end the value). The recursion follows
the list. -/
def decodeGroups (i : Nat) : List Nat → Except DecodeError (Nat × List Nat)
  | [] => .error .truncated
  | b :: rest =>
    if 256 ≤ b then .error .malformed
    else if b < 128 then
      -- A terminator. Zero after a continuation is non-minimal.
      if b = 0 ∧ 0 < i then .error .malformed else .ok (b, rest)
    else if maxBytes ≤ i + 1 then
      -- A continuation as the ninth byte spends the budget.
      .error .malformed
    else
      (decodeGroups (i + 1) rest).map fun (v, r) => (b - 128 + 128 * v, r)

/-- One varint from the front of the input, and the rest. The budget
check builds the proof field (§3.7). The check never fails after
`decodeGroups` succeeds, since nine bytes hold at most 63 bits, but the
check is what gives the field its proof. -/
def decode? (l : List Nat) : Except DecodeError (UVarint × List Nat) := do
  let (n, rest) ← decodeGroups 0 l
  if h : n < limit then return (⟨n, h⟩, rest) else throw .malformed

/-! ## The lemmas behind the law -/

/-- An encoding of a value below `128 ^ k` takes at most `k` bytes. -/
theorem lengthEncodeNatLe {n k : Nat} (h : n < 128 ^ k) (hk : 0 < k) :
    (encodeNat n).length ≤ k := by
  -- `Nat.strongRecOn` is strong induction: the step may use any smaller
  -- value, here `n / 128`.
  induction n using Nat.strongRecOn generalizing k with
  | _ n ih =>
    rw [encodeNat]
    split
    · simp; omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk' : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with rfl | hpos
        · simp at h; omega
        · exact hpos
      have hdiv : n / 128 < 128 ^ k' := by
        rw [Nat.pow_succ] at h
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
      simp only [List.length_cons]
      have := ih (n / 128) (by omega) hdiv hk'
      omega

/-- Every entry of an encoding is a byte. -/
theorem ltOfMemEncodeNat {n x : Nat} (h : x ∈ encodeNat n) : x < 256 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [encodeNat] at h
    split at h
    · simp at h; omega
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · exact ih (n / 128) (by omega) h

/-- `decodeGroups` reads back an encoding from position `i`, with any
rest after it. The encoding must fit the budget left at `i`, and from
the second byte on the value must be nonzero. That is the minimal rule,
and the recursion of `encodeNat` meets it: it recurses on `n / 128`
only when `n ≥ 128`. -/
theorem decodeGroupsEncodeNat (n i : Nat) (rest : List Nat)
    (hmin : i = 0 ∨ 0 < n) (hlen : i + (encodeNat n).length ≤ maxBytes) :
    decodeGroups i (encodeNat n ++ rest) = .ok (n, rest) := by
  induction n using Nat.strongRecOn generalizing i with
  | _ n ih =>
    rw [encodeNat] at hlen ⊢
    split
    · next hn =>
      -- The single byte is the terminator `n`, below 256 and nonzero
      -- unless it is the first byte.
      simp [decodeGroups, show ¬256 ≤ n by omega, hn, show ¬(n = 0 ∧ 0 < i) by omega]
    · next hn =>
      simp only [hn, ↓reduceIte, List.length_cons] at hlen
      -- The continuation byte and at least one byte after it fit the
      -- budget left at `i`, so byte `i` is not the ninth.
      have hbudget : ¬maxBytes ≤ i + 1 := by
        have hpos : 0 < (encodeNat (n / 128)).length := by
          rw [encodeNat]; split <;> simp
        omega
      -- The first byte is a continuation, below 256, inside the budget.
      simp only [List.cons_append, decodeGroups]
      simp only [show ¬256 ≤ n % 128 + 128 by omega, show ¬n % 128 + 128 < 128 by omega,
        hbudget, ite_false]
      rw [ih (n / 128) (by omega) (i + 1) (Or.inr (by omega)) (by omega)]
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq, and_true]
      omega

/-- A successful `decodeGroups` consumed exactly an encoding: the value
re-encodes to the bytes it read. From the second byte on the value is
nonzero, so the minimal rule makes the decode unique. -/
theorem encodeNatOfDecodeGroups (i : Nat) :
    ∀ (l : List Nat) (n : Nat) (rest : List Nat),
      decodeGroups i l = .ok (n, rest) → encodeNat n ++ rest = l ∧ (i = 0 ∨ 0 < n) := by
  intro l
  induction l generalizing i with
  | nil => intro n rest h; simp [decodeGroups] at h
  | cons b l ih =>
    intro n rest h
    simp only [decodeGroups] at h
    split at h
    · cases h
    · next hb256 =>
      split at h
      · next hb =>
        split at h
        · cases h
        · next hmin =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_⟩
          · rw [encodeNat]; simp [hb]
          · omega
      · next hb =>
        split at h
        · cases h
        · -- `Except.map` of an `.ok` is the only way to an `.ok`.
          cases hrec : decodeGroups (i + 1) l with
          | error e => simp [hrec, Except.map] at h
          | ok p =>
            obtain ⟨v, r⟩ := p
            simp only [hrec, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hl, hv⟩ := ih (i + 1) v r hrec
            have hv : 0 < v := by omega
            refine ⟨?_, Or.inr (by omega)⟩
            rw [encodeNat]
            -- `↓reduceIte` folds the `if` once the condition is `False`.
            simp only [show ¬b - 128 + 128 * v < 128 by omega, ↓reduceIte]
            have hmod : (b - 128 + 128 * v) % 128 = b - 128 := by omega
            have hdiv : (b - 128 + 128 * v) / 128 = v := by omega
            rw [hmod, hdiv, List.cons_append, hl]
            congr 1
            omega

/-- The encoding of a varint fits the 9-byte budget. -/
theorem lengthEncodeLe (v : UVarint) : (encode v).length ≤ maxBytes := by
  have h : v.val < 128 ^ maxBytes := by
    have := v.isLt
    -- `2 ^ (7 * k) = 128 ^ k`: `Nat.pow_mul` regroups the power, and
    -- `simp` evaluates `2 ^ 7`.
    rw [limit, Nat.pow_mul] at this
    simpa using this
  exact lengthEncodeNatLe h (by decide)

/-! ## The instances -/

instance : Codec UVarint where
  encode := encode
  decode? := decode?

/-- The suffix form: the decode of an encoding, with any rest after it.
A framing layer decodes a length off the front of a buffer and trusts
the split. -/
theorem decodeEncodeSuffix (v : UVarint) (rest : List Nat) :
    decode? (encode v ++ rest) = .ok (v, rest) := by
  unfold decode? encode
  rw [decodeGroupsEncodeNat v.val 0 rest (Or.inl rfl)
    (by simpa [encode] using lengthEncodeLe v)]
  -- The budget check passes on `v.val`, and `↓reduceDIte` takes the
  -- `then` branch of the dependent `if`.
  simp only [bind, Except.bind, v.isLt, ↓reduceDIte]
  rfl

instance : LawfulCodec UVarint where
  decodeEncode v := by
    -- `Codec.encode` and `Codec.decode?` unfold to the module functions.
    show decode? (encode v) = _
    simpa using decodeEncodeSuffix v []
  encodeDecode l v rest h := by
    simp only [Codec.decode?, decode?, bind, Except.bind] at h
    cases hg : decodeGroups 0 l with
    | error e => simp [hg] at h
    | ok p =>
      obtain ⟨n, r⟩ := p
      simp only [hg] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact (encodeNatOfDecodeGroups 0 l n r hg).1
      · cases h

end Varint
