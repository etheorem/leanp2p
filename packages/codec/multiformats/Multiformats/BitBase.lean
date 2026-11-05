import Multiformats.Error

/-!
# Power-of-two alphabets

Groups are read most-significant-bit first. The encoder pads its final
group with zero bits. The decoder checks unused bits and the complete
group count, so incomplete extra groups cannot become valid empty data.
-/

set_option autoImplicit false

namespace Multiformats.BitBase

/-- The available-bit measure decreases at each emitted group. -/
private def flush (bits : Nat) (alphabet : List Char) (acc available : Nat) :
    List Char × Nat × Nat :=
  if 0 < bits ∧ bits ≤ available then
    let shift := available - bits
    let digit := acc / 2 ^ shift % 2 ^ bits
    let (digits, tail, left) := flush bits alphabet (acc % 2 ^ shift) shift
    (alphabet.getD digit '?' :: digits, tail, left)
  else ([], acc, available)
termination_by available
decreasing_by omega

/-- Padding is separate from bit slicing; unpadded forms pass a zero group size. -/
def encode (bits : Nat) (alphabet : String) (padTo : Nat) (bytes : ByteArray) : String := Id.run do
  let mut reversed : List Char := []
  let mut acc := 0
  let mut available := 0
  for b in bytes do
    let (digits, tail, left) := flush bits alphabet.toList (acc * 256 + b.toNat) (available + 8)
    reversed := digits.reverse ++ reversed
    acc := tail
    available := left
  let final := if available > 0 then
    [alphabet.toList.getD (acc * 2 ^ (bits - available)) '?'] else []
  let chars := reversed.reverse ++ final
  let pad := if padTo = 0 then 0 else (padTo - chars.length % padTo) % padTo
  return String.ofList (chars ++ List.replicate pad '=')

/-- Padded forms must use exactly the number of trailing equals signs required. -/
private def removePadding? (text : String) (group : Nat) : Option (List Char) :=
  let chars := text.toList
  let body := chars.takeWhile (· != '=')
  let padding := chars.drop body.length
  let expected := if group = 0 then 0 else (group - body.length % group) % group
  if padding.length = expected ∧ padding.all (· == '=') then some body else none

/-- Case folding belongs to the alphabet. Only the I2P compatibility caller
disables the unused-bit check; registered multibase decoders keep it enabled. -/
def decode? (bits : Nat) (alphabet : String) (foldCase : Bool) (padTo : Nat)
    (text : String) (strictTrailing : Bool := true) : Except Error ByteArray := do
  if bits = 0 || bits > 7 then .error .badBaseValue
  else
    let chars ← match removePadding? text padTo with
      | none => .error .badBaseValue
      | some chars => .ok chars
    let mut output := ByteArray.empty
    let mut acc := 0
    let mut available := 0
    for c in chars do
      let value ← match alphabet.toList.findIdx? (· == (if foldCase then c.toLower else c)) with
        | none => .error .badBaseValue
        | some value => .ok value
      acc := acc * 2 ^ bits + value
      available := available + bits
      if available ≥ 8 then
        let shift := available - 8
        output := output.push (UInt8.ofNat (acc / 2 ^ shift))
        acc := acc % 2 ^ shift
        available := shift
    if (strictTrailing && acc != 0) || chars.length != (output.size * 8 + bits - 1) / bits then
      .error .badBaseValue
    else .ok output

end Multiformats.BitBase
