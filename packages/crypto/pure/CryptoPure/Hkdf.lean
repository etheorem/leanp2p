import CryptoPure.Constants
import CryptoPure.Hmac

/-!
# HKDF

RFC 5869 over HMAC, on the `List Nat` model. `extract` turns input key
material into a pseudorandom key (§2.2), and `expand` derives output
keying material from it (§2.3). Both take the hash, its block size,
and its output length as arguments. The length and prefix theorems
assume that the hash has that output length for every input. This is
the audited copy and the oracle for the W3.3 cross-check (ARCHITECTURE
§4.6).

RFC 5869 caps the output at `255 × HashLen` bytes, because the block
counter is one byte. `expand` returns `none` exactly when the request
exceeds that cap, so each counter used by `expand` fits in one byte.
-/

set_option autoImplicit false

namespace CryptoPure.Hkdf

/-- HKDF-Extract (RFC 5869 §2.2): `HMAC(salt, IKM)`. An empty salt
stands for `HashLen` zero bytes. -/
def extract (hash : List Nat → List Nat) (blockSize hashLen : Nat)
    (salt ikm : List Nat) : List Nat :=
  Hmac.hmac hash blockSize (if salt = [] then List.replicate hashLen 0 else salt) ikm

/-- Generates `count` output blocks, `T(i) ‖ T(i+1) ‖ …` (RFC 5869
§2.3). `prev` is `T(i-1)`, empty before the first block, and `i` is the
next counter. `expand` keeps the counter within one byte. Recursion
on `count` lets Lean check termination without a separate measure. -/
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

/-- `count` output blocks hold `count × HashLen` bytes. -/
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

/-- A request under the cap fits in its rounded-up block count.
For a zero-length hash, the cap permits only an empty request. -/
private theorem leDivCeilMul {l n : Nat} (hcap : l ≤ maxBlocks * n) :
    l ≤ (l + n - 1) / n * n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst n
    simp_all
  · have hdm := Nat.div_add_mod (l + n - 1) n
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
    have := leDivCeilMul (l := l) (n := hashLen) (by assumption)
    omega
  · simp at h

/-- For the same inputs, a successful shorter output is a prefix of
a successful longer output. -/
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
    exact leDivCeilMul (by assumption)
  generalize blocks hash blockSize prk info [] 1 ((l₁ + hashLen - 1) / hashLen) = A at hpre hl₁ ⊢
  generalize blocks hash blockSize prk info [] 1 ((l₁ + hashLen - 1) / hashLen + extra) = B
    at hpre ⊢
  -- `A` is a prefix of `B` long enough for `l₁`, so both cuts can read `B`.
  rw [hpre, List.take_take, Nat.min_eq_left hl₁, ← Nat.min_eq_left hle, ← List.take_take]
  exact List.take_prefix _ _
end

/-- HKDF-Extract over SHA-256 keys HMAC with 32 zero bytes when the salt
is empty. -/
example (ikm : List Nat) : extractSha256 [] ikm = Hmac.sha256 (List.replicate 32 0) ikm :=
  rfl

/-- HKDF-Expand over SHA-256 rejects 8161 bytes, one above its cap of
`255 × 32`. -/
example (prk info : List Nat) : expandSha256 prk info 8161 = none :=
  (expandEqNoneIff _ _ _ _).mpr (by decide)

end CryptoPure.Hkdf
