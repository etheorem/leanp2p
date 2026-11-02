import CryptoPure.Constants
import CryptoPure.Hmac

/-!
# HKDF

RFC 5869 over HMAC, on the `List Nat` model. `extract` turns input key
material into a pseudorandom key (§2.2), and `expand` stretches that
key into output keying material (§2.3). Like HMAC, both take the hash
and its block size as arguments, and the theorems hold for any hash
with a fixed output length. This is the audited copy, and the oracle
of the W3.3 cross-check (ARCHITECTURE §4.6).

RFC 5869 caps the output at `255 × HashLen` bytes, because the block
counter is one byte. `expand` returns `none` past the cap and only
then, so every counter it writes fits in one byte, as the RFC
requires.
-/

set_option autoImplicit false

namespace CryptoPure.Hkdf

/-- HKDF-Extract (RFC 5869 §2.2): `HMAC(salt, IKM)`. An empty salt
stands for `HashLen` zero bytes. -/
def extract (hash : List Nat → List Nat) (blockSize hashLen : Nat)
    (salt ikm : List Nat) : List Nat :=
  Hmac.hmac hash blockSize (if salt = [] then List.replicate hashLen 0 else salt) ikm

/-- The output blocks `T(i) ‖ T(i+1) ‖ …`, `count` of them (RFC 5869
§2.3). `prev` is `T(i-1)`, empty before the first block, and `i` is the
one-byte counter of the next block. The recursion runs on `count`, so
Lean accepts it as total with no measure to state. -/
def blocks (hash : List Nat → List Nat) (blockSize : Nat) (prk info : List Nat) :
    List Nat → Nat → Nat → List Nat
  | _, _, 0 => []
  | prev, i, count + 1 =>
    let t := Hmac.hmac hash blockSize prk (prev ++ info ++ [i])
    t ++ blocks hash blockSize prk info t (i + 1) count

/-- HKDF-Expand (RFC 5869 §2.3): the first `l` bytes of
`T(1) ‖ T(2) ‖ …`. `none` means `l` is above `255 × HashLen`. -/
def expand (hash : List Nat → List Nat) (blockSize hashLen : Nat)
    (prk info : List Nat) (l : Nat) : Option (List Nat) :=
  if l ≤ maxBlocks * hashLen then
    some ((blocks hash blockSize prk info [] 1 ((l + hashLen - 1) / hashLen)).take l)
  else none

/-- HKDF-Extract over SHA-256. -/
def extractSha256 (salt ikm : List Nat) : List Nat :=
  extract Sha256.digest Sha256.blockSize Sha256.digestSize salt ikm

/-- HKDF-Expand over SHA-256. -/
def expandSha256 (prk info : List Nat) (l : Nat) : Option (List Nat) :=
  expand Sha256.digest Sha256.blockSize Sha256.digestSize prk info l

/-! ## The reductions -/

/-- HKDF-Extract is HMAC keyed by the salt. -/
theorem extractEq (hash : List Nat → List Nat) (blockSize hashLen : Nat)
    (salt ikm : List Nat) :
    extract hash blockSize hashLen salt ikm =
      Hmac.hmac hash blockSize (if salt = [] then List.replicate hashLen 0 else salt) ikm :=
  rfl

/-- One step of the RFC 5869 recurrence:
`T(i) = HMAC(PRK, T(i-1) ‖ info ‖ i)`. -/
theorem blocksSucc (hash : List Nat → List Nat) (blockSize : Nat) (prk info prev : List Nat)
    (i count : Nat) :
    blocks hash blockSize prk info prev i (count + 1) =
      Hmac.hmac hash blockSize prk (prev ++ info ++ [i]) ++
        blocks hash blockSize prk info (Hmac.hmac hash blockSize prk (prev ++ info ++ [i]))
          (i + 1) count :=
  rfl

/-! ## The output length and the prefix property -/

section
variable {hash : List Nat → List Nat} {hashLen : Nat}

theorem lengthBlocks (hlen : ∀ m, (hash m).length = hashLen) (blockSize : Nat)
    (prk info prev : List Nat) (i count : Nat) :
    (blocks hash blockSize prk info prev i count).length = count * hashLen := by
  induction count generalizing prev i with
  | zero => simp [blocks]
  | succ count ih =>
    simp only [blocks, List.length_append, ih, Hmac.lengthHmac hlen]
    rw [Nat.succ_mul]
    omega

/-- More blocks extend the stream: `l₁ <+: l₂` says `l₁` is a prefix of
`l₂`. -/
theorem blocksPrefix (blockSize : Nat) (prk info prev : List Nat) (i count extra : Nat) :
    blocks hash blockSize prk info prev i count <+:
      blocks hash blockSize prk info prev i (count + extra) := by
  induction count generalizing prev i with
  | zero => simp [blocks, List.nil_prefix]
  | succ count ih =>
    rw [show count + 1 + extra = (count + extra) + 1 by omega]
    simp only [blocks]
    exact (List.prefix_append_right_inj _).mpr (ih _ _)

/-- `l` bytes fit in `⌈l / n⌉` blocks of `n` bytes. -/
private theorem leDivCeilMul {l n : Nat} (hpos : 0 < n) : l ≤ (l + n - 1) / n * n := by
  have hdm := Nat.div_add_mod (l + n - 1) n
  have hmod := Nat.mod_lt (l + n - 1) hpos
  generalize (l + n - 1) / n = q at *
  generalize (l + n - 1) % n = r at *
  rw [Nat.mul_comm] at hdm
  generalize q * n = p at *
  omega

/-- `expand` fails exactly past the cap of RFC 5869 §2.3. -/
theorem expandEqNoneIff (blockSize : Nat) (prk info : List Nat) (l : Nat) :
    expand hash blockSize hashLen prk info l = none ↔ maxBlocks * hashLen < l := by
  unfold expand
  split <;> simp <;> omega

/-- Under the cap, the output is exactly `l` bytes. -/
theorem lengthExpand (hlen : ∀ m, (hash m).length = hashLen) (blockSize : Nat)
    (prk info : List Nat) {l : Nat} {okm : List Nat}
    (h : expand hash blockSize hashLen prk info l = some okm) : okm.length = l := by
  unfold expand at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rw [List.length_take, lengthBlocks hlen]
    rcases Nat.eq_zero_or_pos hashLen with h0 | hpos
    · -- A zero-length hash leaves no room under the cap: `l` is 0.
      subst h0
      omega
    · have := leDivCeilMul (l := l) hpos
      omega
  · simp at h

/-- A shorter output is a prefix of a longer one: asking for fewer
bytes never changes the bytes it returns. -/
theorem expandPrefix (hlen : ∀ m, (hash m).length = hashLen) (blockSize : Nat)
    (prk info : List Nat) {l₁ l₂ : Nat} {okm₁ okm₂ : List Nat} (hle : l₁ ≤ l₂)
    (h₁ : expand hash blockSize hashLen prk info l₁ = some okm₁)
    (h₂ : expand hash blockSize hashLen prk info l₂ = some okm₂) : okm₁ <+: okm₂ := by
  unfold expand at h₁ h₂
  split at h₁ <;> split at h₂ <;> simp only [Option.some.injEq, reduceCtorEq] at h₁ h₂
  subst h₁ h₂
  have hc : (l₁ + hashLen - 1) / hashLen ≤ (l₂ + hashLen - 1) / hashLen :=
    Nat.div_le_div_right (by omega)
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hc
  rw [hextra]
  -- Both outputs are prefixes of the longer block stream, cut at `l₁` and `l₂`.
  have hpre := blocksPrefix (hash := hash) blockSize prk info [] 1
    ((l₁ + hashLen - 1) / hashLen) extra
  rw [List.prefix_iff_eq_take] at hpre
  have hl₁ : l₁ ≤ (blocks hash blockSize prk info [] 1 ((l₁ + hashLen - 1) / hashLen)).length := by
    rw [lengthBlocks hlen]
    rcases Nat.eq_zero_or_pos hashLen with h0 | hpos
    · subst h0
      omega
    · exact leDivCeilMul hpos
  generalize blocks hash blockSize prk info [] 1 ((l₁ + hashLen - 1) / hashLen) = A at hpre hl₁ ⊢
  generalize blocks hash blockSize prk info [] 1 ((l₁ + hashLen - 1) / hashLen + extra) = B
    at hpre ⊢
  -- `A` is the first `A.length` bytes of `B`, and `l₁ ≤ A.length`, so both cuts read `B`.
  rw [hpre, List.take_take, Nat.min_eq_left hl₁, ← Nat.min_eq_left hle, ← List.take_take]
  exact List.take_prefix _ _
end

/-- HKDF-Extract over SHA-256 keys HMAC with 32 zero bytes when the salt
is empty. -/
example (ikm : List Nat) : extractSha256 [] ikm = Hmac.sha256 (List.replicate 32 0) ikm :=
  rfl

/-- 8161 bytes is one past `255 × 32`, so HKDF-Expand over SHA-256
refuses it. -/
example (prk info : List Nat) : expandSha256 prk info 8161 = none :=
  (expandEqNoneIff _ _ _ _).mpr (by decide)

end CryptoPure.Hkdf
