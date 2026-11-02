/-!
# Temporary byte interface

Until W1.2 (`base/bytes`) merges, this module supplies the byte
conversions that this package and its suite need. They live under
`CryptoPure.Mock.Bytes` and import nothing from the real package
(RULES.md, "Working ahead of the tree"). Each `opaque` declaration has
an executable body for the suite. The kernel can't unfold it, so
proofs don't depend on its definition. Replace this module with
`import Bytes` when W1.2 lands.
-/

set_option autoImplicit false

namespace CryptoPure.Mock.Bytes

/-- One byte per model value, taken mod 256 (W1.2, `Bytes.ofNatList`). -/
opaque ofNatList (bs : List Nat) : ByteArray :=
  (bs.map UInt8.ofNat).toByteArray

/-- The model view of a byte array, with every entry below 256 (W1.2,
`Bytes.toNatList`). -/
opaque toNatList (bs : ByteArray) : List Nat :=
  bs.toList.map UInt8.toNat

/-- The UTF-8 bytes of a string (W1.2, `Bytes.ofString`). -/
opaque ofString (s : String) : ByteArray :=
  s.toUTF8

/-- The value of one hex digit, either case. -/
private def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Reads two hex digits per byte. Returns `none` for an odd count or
a non-hex digit. -/
private def hexPairs? : List Char → Option (List Nat)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest => do
    let h ← hexDigit? hi
    let l ← hexDigit? lo
    let tail ← hexPairs? rest
    pure ((h * 16 + l) :: tail)

/-- Hex text to bytes. `none` means an odd length or a non-hex digit
(W1.2, `Bytes.ofHex?`). -/
opaque ofHex? (s : String) : Option ByteArray :=
  (hexPairs? s.toList).map fun bs => (bs.map UInt8.ofNat).toByteArray

end CryptoPure.Mock.Bytes
