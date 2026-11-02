/-!
# Preprocessing

FIPS 180-4 §5 prepares a message for each hash in two steps. Padding
(§5.1) appends a `1` bit, the fewest `0` bits that fit, and the
message length in bits as a big-endian field. Parsing (§5.2) cuts the
padded message into blocks. The three hashes differ in two sizes only:
SHA-1 and SHA-256 use 64-byte blocks with an 8-byte length field, and
SHA-512 uses 128-byte blocks with a 16-byte field. This module states
both steps once, over those two sizes, and proves the properties §5.1
demands. The big-endian conversions of §3.1 sit here too, because each
hash reads its message words and writes its digest through them.

The model is `List Nat`, one byte per entry (ARCHITECTURE §4.2). A
message here is always whole bytes, so the `1` bit and the seven `0`
bits after it form the one byte `0x80`.
-/

set_option autoImplicit false

namespace CryptoPure.Preprocess

/-! ## Big-endian conversions (FIPS 180-4 §3.1) -/

/-- The low `n` bytes of `x`, most significant first. -/
def beBytes : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => beBytes n (x / 256) ++ [x % 256]

/-- The number a big-endian byte string stands for. -/
def ofBeBytes (bs : List Nat) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b) 0

/-- The 32-bit word in the first four bytes, big-endian. -/
def be32 (bs : List Nat) : UInt32 :=
  (ofBeBytes (bs.take 4)).toUInt32

/-- The 64-bit word in the first eight bytes, big-endian. -/
def be64 (bs : List Nat) : UInt64 :=
  (ofBeBytes (bs.take 8)).toUInt64

/-- The four bytes of a 32-bit word, big-endian. -/
def word32Bytes (w : UInt32) : List Nat :=
  beBytes 4 w.toNat

/-- The eight bytes of a 64-bit word, big-endian. -/
def word64Bytes (w : UInt64) : List Nat :=
  beBytes 8 w.toNat

theorem lengthBeBytes (n x : Nat) : (beBytes n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [beBytes, ih]

theorem ltOfMemBeBytes (n x : Nat) : ∀ b ∈ beBytes n x, b < 256 := by
  induction n generalizing x with
  | zero => simp [beBytes]
  | succ n ih =>
    intro b hb
    simp only [beBytes, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact ih (x / 256) b hb
    · omega

theorem ofBeBytesAppendSingleton (bs : List Nat) (b : Nat) :
    ofBeBytes (bs ++ [b]) = ofBeBytes bs * 256 + b := by
  simp [ofBeBytes, List.foldl_append]

/-- Decoding the bytes gives back the value, reduced to `n` bytes. -/
theorem ofBeBytesBeBytes (n x : Nat) : ofBeBytes (beBytes n x) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [beBytes, ofBeBytes, Nat.mod_one]
  | succ n ih =>
    rw [beBytes, ofBeBytesAppendSingleton, ih, Nat.pow_succ', Nat.mod_mul]
    generalize x / 256 % 256 ^ n = y
    omega

theorem lengthWord32Bytes (w : UInt32) : (word32Bytes w).length = 4 :=
  lengthBeBytes 4 w.toNat

theorem lengthWord64Bytes (w : UInt64) : (word64Bytes w).length = 8 :=
  lengthBeBytes 8 w.toNat

/-- Reading back the bytes of a word gives the word. -/
theorem be32Word32Bytes (w : UInt32) : be32 (word32Bytes w) = w := by
  have hlt : w.toNat < 256 ^ 4 := w.toNat_lt
  simp only [be32, word32Bytes]
  rw [List.take_of_length_le (by simp [lengthBeBytes]), ofBeBytesBeBytes,
    Nat.mod_eq_of_lt hlt]
  exact UInt32.ofNat_toNat

/-! ## Padding (FIPS 180-4 §5.1) -/

/-- The number of zero bytes between the `0x80` byte and the length
field: the fewest that bring the padded length to a multiple of the
block size. -/
def zeroCount (blockSize lengthBytes len : Nat) : Nat :=
  (blockSize - (len + 1 + lengthBytes) % blockSize) % blockSize

/-- The padded message: the message, the `0x80` byte, `zeroCount` zero
bytes, and the bit length as a `lengthBytes`-byte big-endian field. -/
def pad (blockSize lengthBytes : Nat) (msg : List Nat) : List Nat :=
  msg ++ [0x80] ++ List.replicate (zeroCount blockSize lengthBytes msg.length) 0 ++
    beBytes lengthBytes (8 * msg.length)

theorem lengthPad (blockSize lengthBytes : Nat) (msg : List Nat) :
    (pad blockSize lengthBytes msg).length =
      msg.length + 1 + zeroCount blockSize lengthBytes msg.length + lengthBytes := by
  simp [pad, lengthBeBytes]
  omega

theorem zeroCountLt {blockSize : Nat} (h : 0 < blockSize) (lengthBytes len : Nat) :
    zeroCount blockSize lengthBytes len < blockSize :=
  Nat.mod_lt _ h

/-- The padded length is a whole number of blocks. -/
theorem padLengthMod {blockSize : Nat} (h : 0 < blockSize) (lengthBytes : Nat)
    (msg : List Nat) : (pad blockSize lengthBytes msg).length % blockSize = 0 := by
  rw [lengthPad, zeroCount]
  generalize msg.length = len
  have hr := Nat.mod_lt (len + 1 + lengthBytes) h
  generalize hrdef : (len + 1 + lengthBytes) % blockSize = r at hr
  have hsum : len + 1 + (blockSize - r) % blockSize + lengthBytes =
      (len + 1 + lengthBytes) + (blockSize - r) % blockSize := by omega
  rw [hsum, Nat.add_mod, hrdef]
  by_cases hr0 : r = 0
  · subst hr0
    simp
  · rw [Nat.mod_eq_of_lt (show blockSize - r < blockSize by omega),
      Nat.mod_eq_of_lt (show blockSize - r < blockSize by omega),
      show r + (blockSize - r) = blockSize by omega, Nat.mod_self]

/-- No shorter zero run reaches a whole number of blocks. -/
theorem zeroCountLe {blockSize : Nat} (h : 0 < blockSize) {lengthBytes len k : Nat}
    (hk : (len + 1 + k + lengthBytes) % blockSize = 0) :
    zeroCount blockSize lengthBytes len ≤ k := by
  unfold zeroCount
  have hr := Nat.mod_lt (len + 1 + lengthBytes) h
  generalize hrdef : (len + 1 + lengthBytes) % blockSize = r at hr
  by_cases hr0 : r = 0
  · subst hr0
    simp
  · rw [Nat.mod_eq_of_lt (show blockSize - r < blockSize by omega)]
    -- `r + k` is a positive multiple of the block size, so it is at least one block.
    have hrk : (r + k) % blockSize = 0 := by
      rw [← hrdef, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        show len + 1 + lengthBytes + k = len + 1 + k + lengthBytes by omega]
      exact hk
    have hle : blockSize ≤ r + k :=
      Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hrk)
    omega

/-- The message is a prefix of its padding. `l₁ <+: l₂` is Lean's
notation for "`l₁` is a prefix of `l₂`". -/
theorem prefixPad (blockSize lengthBytes : Nat) (msg : List Nat) :
    msg <+: pad blockSize lengthBytes msg := by
  unfold pad
  simp only [List.append_assoc]
  exact List.prefix_append _ _

/-- The byte after the message is `0x80`. -/
theorem padMarker (blockSize lengthBytes : Nat) (msg : List Nat) :
    (pad blockSize lengthBytes msg)[msg.length]? = some 0x80 := by
  simp [pad, List.append_assoc]

/-- The bytes between the `0x80` byte and the length field are zero. -/
theorem padZeros (blockSize lengthBytes : Nat) (msg : List Nat) :
    ((pad blockSize lengthBytes msg).drop (msg.length + 1)).take
        (zeroCount blockSize lengthBytes msg.length) =
      List.replicate (zeroCount blockSize lengthBytes msg.length) 0 := by
  simp [pad, List.append_assoc, List.drop_append, List.take_append]

/-- The last field holds the message length in bits, modulo
`2 ^ (8 * lengthBytes)`. -/
theorem padLengthField (blockSize lengthBytes : Nat) (msg : List Nat) :
    ofBeBytes ((pad blockSize lengthBytes msg).drop
        (msg.length + 1 + zeroCount blockSize lengthBytes msg.length)) =
      8 * msg.length % 256 ^ lengthBytes := by
  have hlen : (msg ++ [0x80] ++ List.replicate (zeroCount blockSize lengthBytes msg.length) 0).length =
      msg.length + 1 + zeroCount blockSize lengthBytes msg.length := by
    simp
    omega
  rw [pad, List.drop_left' hlen, ofBeBytesBeBytes]

/-! ## Parsing (FIPS 180-4 §5.2) -/

/-- Cuts a byte string into blocks of `blockSize` bytes. The last block
is shorter when the length is not a multiple of the block size; padding
rules that case out (`lengthOfMemBlocks`). The recursion stops on the
remaining length, so Lean accepts the definition as total. -/
def blocks (blockSize : Nat) (bs : List Nat) : List (List Nat) :=
  -- The guard is named with a leading `_`: only `decreasing_by` reads it,
  -- and the unused-variable linter does not see that use.
  if _hstop : blockSize = 0 ∨ bs = [] then []
  else bs.take blockSize :: blocks blockSize (bs.drop blockSize)
termination_by bs.length
decreasing_by
  -- `_hstop` is false here: the block size is positive and the list is not empty.
  have hb : 0 < blockSize := Nat.pos_of_ne_zero fun e => _hstop (Or.inl e)
  have hl : 0 < bs.length := List.length_pos_iff.mpr fun e => _hstop (Or.inr e)
  simp only [List.length_drop]
  omega

/-- Cutting loses no byte. The proof inducts with `blocks.induct`, the
induction principle Lean derives from the recursion of `blocks`: one
case where the cut stops, and one where it takes a block and recurses. -/
theorem flattenBlocks {blockSize : Nat} (h : 0 < blockSize) (bs : List Nat) :
    (blocks blockSize bs).flatten = bs := by
  induction bs using blocks.induct blockSize with
  | case1 bs hc =>
    rw [blocks, dite_eq_left hc]
    rcases hc with hc | rfl
    · subst hc
      exact absurd h (Nat.lt_irrefl 0)
    · rfl
  | case2 bs hc ih =>
    rw [blocks, dite_eq_right hc, List.flatten_cons, ih, List.take_append_drop]

/-- When the length is a whole number of blocks, every block is full. -/
theorem lengthOfMemBlocks {blockSize : Nat} (bs : List Nat)
    (hbs : bs.length % blockSize = 0) : ∀ c ∈ blocks blockSize bs, c.length = blockSize := by
  induction bs using blocks.induct blockSize with
  | case1 bs hc =>
    rw [blocks, dite_eq_left hc]
    simp
  | case2 bs hc ih =>
    rw [blocks, dite_eq_right hc]
    have hl : 0 < bs.length := List.length_pos_iff.mpr (by simp_all)
    have hle : blockSize ≤ bs.length :=
      Nat.le_of_dvd hl (Nat.dvd_of_mod_eq_zero hbs)
    intro c hcmem
    simp only [List.mem_cons] at hcmem
    rcases hcmem with rfl | hcmem
    · simp [hle]
    · apply ih _ c hcmem
      rw [List.length_drop]
      exact Nat.sub_mod_eq_zero_of_mod_eq (by rw [hbs, Nat.mod_self])

/-- Every block of a padded message is full, so the word reads of a
compression function never run past a block. -/
theorem lengthOfMemBlocksPad {blockSize : Nat} (h : 0 < blockSize) (lengthBytes : Nat)
    (msg : List Nat) :
    ∀ c ∈ blocks blockSize (pad blockSize lengthBytes msg), c.length = blockSize :=
  lengthOfMemBlocks _ (padLengthMod h lengthBytes msg)

/-- The worked example of FIPS 180-4 §5.1.1: "abc" is 24 bits, so 52
zero bytes follow `0x80`, and the length field reads 24. -/
example : pad 64 8 [0x61, 0x62, 0x63] =
    [0x61, 0x62, 0x63, 0x80] ++ List.replicate 52 0 ++ [0, 0, 0, 0, 0, 0, 0, 24] := by
  decide

end CryptoPure.Preprocess
