import Multiformats.Error

/-!
# Percent escapes over UTF-8 bytes

An escape carries one byte. Decoding validates the whole UTF-8 result,
so a partial multibyte sequence cannot become a different path.
-/

set_option autoImplicit false

namespace Multiformats.Multiaddr

/-- Only ASCII hexadecimal digits belong inside an escape. -/
private def hexValue? (byte : Nat) : Option Nat :=
  if 48 ≤ byte ∧ byte ≤ 57 then some (byte - 48)
  else if 65 ≤ byte ∧ byte ≤ 70 then some (byte - 65 + 10)
  else if 97 ≤ byte ∧ byte ≤ 102 then some (byte - 97 + 10)
  else none

/-- Reversed accumulation keeps path decoding linear in its byte count. -/
private def unescape (reversed : List Nat) : List Nat → Except Error (List Nat)
  | [] => .ok reversed.reverse
  | 37 :: high :: low :: rest =>
      match hexValue? high, hexValue? low with
      | some a, some b => unescape ((a * 16 + b) :: reversed) rest
      | _, _ => .error .badValue
  | 37 :: _ => .error .badValue
  | byte :: rest => unescape (byte :: reversed) rest

/-- Raw UTF-8 and escaped bytes enter the same validation boundary. -/
def percentDecode? (text : String) : Except Error String := do
  let bytes ← unescape [] (text.toUTF8.toList.map UInt8.toNat)
  match Bytes.toString? (Bytes.ofNatList bytes) with
  | some text => .ok text
  | none => .error .badValue

/-- RFC 3986 unreserved bytes pass through unchanged. -/
private def unreserved (b : Nat) : Bool :=
  (65 ≤ b ∧ b ≤ 90) || (97 ≤ b ∧ b ≤ 122) || (48 ≤ b ∧ b ≤ 57) ||
    b == 45 || b == 46 || b == 95 || b == 126

/-- Escapes print uppercase digits, independently of input spelling. -/
private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 65 + n - 10)

/-- Each byte of a non-ASCII character receives its own escape. -/
def percentEncode (text : String) : String := Id.run do
  let mut reversed : List Char := []
  for byte in text.toUTF8 do
    let b := byte.toNat
    if unreserved b then reversed := Char.ofNat b :: reversed
    else reversed := hexDigit (b % 16) :: hexDigit (b / 16) :: '%' :: reversed
  return String.ofList reversed.reverse

end Multiformats.Multiaddr
