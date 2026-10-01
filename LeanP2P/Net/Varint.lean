/-!
# Unsigned varint (uvarint, LEB128)

Per multiformats/unsigned-varint, the framing integer used by multiaddr and
multistream-select. The spec's rules (README, "Rules") are enforced and
machine-checked here:

- minimal encodings only: after any continuation byte the remaining value
  must be nonzero, so `0x81 0x00` (which decodes to 1 in Go) is rejected;
- at most 9 bytes (63 bits): `decode?` runs with fuel 9, so a 10-byte input
  fails.

Two models: a pure `List Nat` core carrying the round-trip and inverse
theorems, and `ByteArray` entry points for the IO edge that report the
number of bytes consumed.
-/

namespace LeanP2P.Varint

def encode : Nat → List Nat
  | n => if n < 128 then [n] else (n % 128 + 128) :: encode (n / 128)
termination_by n => n
decreasing_by omega

/-- Fuel bounds the varint length (max 9 bytes for `decode?`). A recursive
value of `0` after a continuation byte means the high group is zero: a
non-minimal encoding. -/
def decodeF : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, b :: bs =>
      if b < 128 then some (b, bs)
      else
        match decodeF f bs with
        | some (v, bs') => if v = 0 then none else some (128 * v + (b - 128), bs')
        | none => none

/-- Spec-conformant decoder: minimal encodings only, at most 9 bytes (63 bits). -/
def decode? : List Nat → Option (Nat × List Nat) := decodeF 9

def encodeB (n : Nat) : ByteArray :=
  (encode n).map UInt8.ofNat |>.toByteArray

/-- ByteArray decoder: `(value, bytes consumed)` reading from index `i`. -/
def decodeBAt? : Nat → ByteArray → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | f + 1, b, i =>
      match b[i]? with
      | none => none
      | some v =>
          if v.toNat < 128 then some (v.toNat, 1)
          else
            match decodeBAt? f b (i + 1) with
            | some (x, c) => if x = 0 then none else some (128 * x + (v.toNat - 128), c + 1)
            | none => none

/-- `decodeB? b i`: value and bytes consumed. -/
def decodeB? (b : ByteArray) (i : Nat) : Option (Nat × Nat) := decodeBAt? 9 b i

/-! ## Properties -/

theorem encode_small {n : Nat} (h : n < 128) : encode n = [n] := by
  rw [encode, if_pos h]

theorem encode_big {n : Nat} (h : 128 ≤ n) : encode n = (n % 128 + 128) :: encode (n / 128) := by
  rw [encode, if_neg (by omega)]

/-- A successful decode consumes exactly the encoding of the decoded value:
in particular every accepted varint is minimal and self-delimiting. -/
theorem decodeF_encode_inv : ∀ f n rest bs,
    decodeF f bs = some (n, rest) → (∀ x ∈ bs, x < 256) → bs = encode n ++ rest := by
  intro f
  induction f with
  | zero => intro n rest bs h; simp [decodeF] at h
  | succ f ih =>
    intro n rest bs h all
    match bs with
    | [] => simp [decodeF] at h
    | b :: bs' =>
      rw [decodeF] at h
      by_cases hb : b < 128
      · rw [if_pos hb] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [encode_small hb]
        rfl
      · rw [if_neg hb] at h
        match hf : decodeF f bs' with
        | none => rw [hf] at h; exact absurd h (by simp)
        | some (v, bs'') =>
          rw [hf] at h
          have h' : (if v = 0 then none else some (128 * v + (b - 128), bs''))
              = some (n, rest) := h
          by_cases hv : v = 0
          · rw [if_pos hv] at h'; exact absurd h' (by simp)
          · rw [if_neg hv] at h'
            simp only [Option.some.injEq, Prod.mk.injEq] at h'
            obtain ⟨hn', hrest⟩ := h'
            -- bs' = encode v ++ bs'' by IH
            have hmem : ∀ x ∈ bs', x < 256 := fun x hx =>
              all x (List.mem_cons.2 (Or.inr hx))
            have hbs : bs' = encode v ++ bs'' :=
              ih v bs'' bs' hf hmem
            have hb256 : b < 256 := all b (List.mem_cons.2 (Or.inl rfl))
            have hge : 128 ≤ n := by omega
            rw [encode_big hge, List.cons_append,
                show n % 128 + 128 = b from by omega,
                show n / 128 = v from by omega,
                hbs, hrest]

theorem decode_encode_inv {bs : List Nat} {n : Nat} {rest : List Nat}
    (h : decode? bs = some (n, rest)) (all : ∀ x ∈ bs, x < 256) :
    bs = encode n ++ rest :=
  decodeF_encode_inv 9 n rest bs h all

/-- The README's non-minimal counter-example `0x81 0x00` is rejected
(deciding the closed computation). -/
theorem decode_nonminimal : decode? [0x81, 0x00] = none := rfl

/-- A 10-byte varint exceeds the 9-byte limit and is rejected. -/
theorem decode_too_long : decode? (List.replicate 9 255 ++ [1]) = none := rfl

/-- Round trip through any context: decoding an encoding off a longer buffer
yields the value and the untouched rest. -/
theorem decodeF_encode_app : ∀ n rest, n < 2 ^ 63 →
    ∀ f, (encode n).length ≤ f → decodeF f (encode n ++ rest) = some (n, rest) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro rest hn f hf
    by_cases h : n < 128
    · match f with
      | 0 =>
        rw [encode_small h] at hf
        simp at hf
      | f' + 1 =>
        rw [encode_small h, List.cons_append, decodeF, if_pos h]
        rfl
    · have h128 : 128 ≤ n := by omega
      match f with
      | 0 =>
        have hne : encode n ≠ [] := by rw [encode_big h128]; simp
        simp at hf
        exact absurd hf hne
      | f' + 1 =>
        have hlt : n / 128 < n := by omega
        have hlen : (encode (n / 128)).length ≤ f' := by
          have hlen' : (encode n).length = (encode (n / 128)).length + 1 := by
            rw [encode_big h128]; simp
          omega
        rw [encode_big h128, List.cons_append, decodeF]
        rw [if_neg (show ¬(n % 128 + 128 < 128) by omega)]
        rw [ih (n / 128) hlt rest (by omega : n / 128 < 2 ^ 63) f' hlen]
        have h' : (if n / 128 = 0 then none
                   else some (128 * (n / 128) + (n % 128 + 128 - 128), rest))
              = some (n, rest) := by
          rw [if_neg (show ¬(n / 128 = 0) by omega),
              show 128 * (n / 128) + (n % 128 + 128 - 128) = n by omega]
        exact h'

/-- Encoding length: values inside the 63-bit budget need at most 9 bytes. -/
theorem encode_length_le (n : Nat) : n < 2 ^ 63 → (encode n).length ≤ 9 := by
  have h128 : (2 : Nat) ^ 63 = 128 ^ 9 := by rfl
  intro h
  have general : ∀ k n, n < 128 ^ (k + 1) → (encode n).length ≤ k + 1 := by
    intro k
    induction k with
    | zero =>
      intro n hn
      rw [Nat.pow_succ] at hn
      have hn128 : n < 128 := by simpa using hn
      rw [encode_small hn128]
      show 1 ≤ 0 + 1
      omega
    | succ k ih =>
      intro n hn
      rw [Nat.pow_succ] at hn
      by_cases hb : n < 128
      · rw [encode_small hb]; simp
      · have h128le : 128 ≤ n := by omega
        have hlt : n / 128 < n := by omega
        have hrec : n / 128 < 128 ^ (k + 1) :=
          (Nat.div_lt_iff_lt_mul (by omega)).mpr hn
        have := ih (n / 128) hrec
        rw [encode_big h128le]
        simp
        omega
  exact general 8 n (by rw [← h128]; exact h)

theorem decode_encode (n : Nat) (h : n < 2 ^ 63) :
    decode? (encode n) = some (n, []) := by
  show decodeF 9 _ = _
  rw [← List.append_nil (encode n)]
  exact decodeF_encode_app n [] h 9 (encode_length_le n h)

end LeanP2P.Varint
