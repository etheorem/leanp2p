import Multiformats.Error

/-!
# Integer-base byte conversions

Decimal, base36, and the two base58 alphabets share this conversion.
Leading zero bytes have their own zero digits, separate from the
integer value of the remaining bytes.
-/

set_option autoImplicit false

namespace Multiformats.Radix

/-- The decreasing quotient makes conversion total, including a bad radix. -/
private def digits (radix n : Nat) : List Nat :=
  if 1 < radix ∧ 0 < n then digits radix (n / radix) ++ [n % radix] else []
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The low digit is emitted last in the big-endian byte model. -/
private def bytesOfNat (n : Nat) : List Nat := digits 256 n

/-- Encode with a fixed alphabet of at least two distinct characters. -/
def encode (alphabet : String) (bytes : ByteArray) : String :=
  let chars := alphabet.toList
  let zeros := (bytes.toList.takeWhile (· == 0)).length
  let value := bytes.toList.foldl (fun n b => n * 256 + b.toNat) 0
  String.ofList (List.replicate zeros (chars.getD 0 '0') ++
    (digits chars.length value).map (fun d => chars.getD d '?'))

/-- Case folding is enabled only for alphabets where it preserves digit values. -/
private def digit? (alphabet : List Char) (foldCase : Bool) (c : Char) : Option Nat :=
  match alphabet.findIdx? (· == c) with
  | some index => some index
  | none =>
      if foldCase then alphabet.findIdx? (· == c.toLower)
      else none

/-- Leading zero digits recover zero bytes without changing the integer body. -/
def decode? (alphabet : String) (foldCase : Bool) (text : String) : Except Error ByteArray := do
  let chars := alphabet.toList
  if chars.length < 2 then .error .badBaseValue
  else
    let input := text.toList
    let zeros := (input.takeWhile (· == chars.getD 0 '0')).length
    let value ← (input.drop zeros).foldlM (fun n c =>
      match digit? chars foldCase c with
      | some d => .ok (n * chars.length + d)
      | none => .error .badBaseValue) 0
    .ok (Bytes.ofNatList (List.replicate zeros 0 ++ bytesOfNat value))

end Multiformats.Radix
