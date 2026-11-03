import Bytes.Model

/-!
# Hex and UTF-8 conversions

The `String` and hex forms of the byte floor (ARCHITECTURE §4.2). The
model stays the source of truth: `toHex` renders a `ByteArray` as two
lowercase digits per byte, and `ofHex?` reads that form back. `ofString`
and `toString?` bridge to UTF-8.

Both pairs carry proved round-trip theorems. Every `ByteArray` survives
`ofHex? (toHex b)`, and every `String` survives `toString? (ofString s)`
through its UTF-8 validity invariant.

## Why the nibble proof enumerates

`decide` closes a goal on a closed `Char` comparison, but Lean carries
no `Fintype UInt8`, so a goal quantified over `b : UInt8` cannot be
decided directly. `hexVal?HexDigit` therefore enumerates the sixteen
nibble values, and every other proof composes that lemma over `Nat`
arithmetic.
-/

set_option autoImplicit false

namespace Bytes

/-- Render one nibble, a value in `0..15`, as a lowercase hexadecimal
character. Values at or above 16 render as the digit `a` plus the
excess; callers pass a nibble. -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n)
  else Char.ofNat ('a'.toNat + (n - 10))

/-- Parse one lowercase hexadecimal character into its nibble value.
Returns `none` for a character outside `0..9` and `a..f`. -/
private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The UTF-8 bytes of a string. -/
def ofString (s : String) : ByteArray := s.toUTF8

/-- The string a byte sequence spells in UTF-8. Returns `none` for a
sequence that has no UTF-8 reading, and that is the only meaning of
`none` here (ARCHITECTURE §3.5). -/
def toString? (b : ByteArray) : Option String := String.fromUTF8? b

/-- Every `String` carries valid UTF-8 bytes and decodes back to itself. -/
theorem toString?OfString (s : String) : toString? (ofString s) = some s := by
  simp only [toString?, ofString, String.toUTF8_eq_toByteArray,
    String.fromUTF8?, s.isValidUTF8, ↓reduceDIte]
  rfl

/-- Render a list of bytes as lowercase hexadecimal characters, two per
byte, high nibble first. -/
private def encodeHexChars : List UInt8 → List Char
  | [] => []
  | b :: bs => hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: encodeHexChars bs

/-- Parse pairs of lowercase hexadecimal characters into a list of
bytes. Returns `none` for an odd length or a non-hex character. -/
private def decodeHexChars? : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest =>
    match hexVal? hi, hexVal? lo, decodeHexChars? rest with
    | some h, some l, some bs => some (UInt8.ofNat (h * 16 + l) :: bs)
    | _, _, _ => none

/-- Render a `ByteArray` as a lowercase hexadecimal `String`, two digits
per byte. -/
def toHex (b : ByteArray) : String :=
  String.ofList (encodeHexChars b.data.toList)

/-- Parse a lowercase hexadecimal `String` into a `ByteArray`. Returns
`none` when the length is odd, and for every character outside `0..9`
and `a..f`. -/
def ofHex? (s : String) : Option ByteArray :=
  (decodeHexChars? s.toList).map (fun bs => ⟨bs.toArray⟩)

/-- A rendered nibble parses back to that nibble. Proved by the sixteen
closed cases, because Lean carries no `Fintype UInt8` for `decide` on a
quantified goal. -/
private theorem hexVal?HexDigit (n : Nat) (h : n < 16) : hexVal? (hexDigit n) = some n := by
  match n, h with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide
  | 10, _ => decide
  | 11, _ => decide
  | 12, _ => decide
  | 13, _ => decide
  | 14, _ => decide
  | 15, _ => decide
  | k + 16, h => omega

/-- Every byte round-trips through its two lowercase hexadecimal
characters. -/
private theorem decodeHexByte (b : UInt8) :
    (match hexVal? (hexDigit (b.toNat / 16)), hexVal? (hexDigit (b.toNat % 16)) with
     | some h, some l => some (UInt8.ofNat (h * 16 + l))
     | _, _ => none) = some b := by
  have h1 : b.toNat / 16 < 16 := by
    have := UInt8.toNat_lt b
    omega
  have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [hexVal?HexDigit (b.toNat / 16) h1, hexVal?HexDigit (b.toNat % 16) h2]
  show some (UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16)) = some b
  have hidx : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod b.toNat 16
  rw [hidx, UInt8.ofNat_toNat]

/-- A byte list round-trips through its hexadecimal characters. -/
private theorem decodeHexChars?EncodeHexChars (bs : List UInt8) :
    decodeHexChars? (encodeHexChars bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have h1 : b.toNat / 16 < 16 := by
      have := UInt8.toNat_lt b
      omega
    have h2 : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    simp only [encodeHexChars, decodeHexChars?, ih,
      hexVal?HexDigit (b.toNat / 16) h1, hexVal?HexDigit (b.toNat % 16) h2]
    have hidx : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod b.toNat 16
    rw [hidx, UInt8.ofNat_toNat]

/-- The hex round trip on the public surface: every `ByteArray` comes
back unchanged from `ofHex? (toHex b)`. -/
theorem ofHex?ToHex (b : ByteArray) : ofHex? (toHex b) = some b := by
  unfold ofHex? toHex
  rw [String.toList_ofList, decodeHexChars?EncodeHexChars]
  simp only [Option.map]

end Bytes
