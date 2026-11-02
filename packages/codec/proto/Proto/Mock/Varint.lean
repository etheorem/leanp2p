import Proto.Mock.Bytes

/-!
# Temporary unsigned-varint interface

W2.1 is not merged. Executable opaque definitions follow its documented
nine-byte, minimal-form contract. The four axioms below are dependency
contracts, not protobuf results. They must disappear with this mock.
-/

set_option autoImplicit false

namespace Pb.Mock.Varint

open Pb.Mock.Bytes (DecodeError)

/-- The dependency stops after nine groups, including an unterminated last group. -/
def maxBytes : Nat := 9

/-- Nine groups of seven bits fit exactly in this range. -/
def limit : Nat := 2 ^ 63

/-- The range proof is erased at runtime. -/
structure UVarint where
  val : Nat
  isLt : val < limit
  deriving DecidableEq, Repr

/-- Executable reference encoder; callers use the opaque interface below. -/
private def encodeCore (n : Nat) : List Nat :=
  if n < 128 then [n]
  else (n % 128 + 128) :: encodeCore (n / 128)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- The mock preserves the frozen argument type. -/
opaque encode (v : UVarint) : List Nat := encodeCore v.val

/-- The last permitted continuation byte is malformed, even without a suffix. -/
private def decodeCore : Nat → List Nat → Except DecodeError (Nat × List Nat)
  | 0, _ => .error .malformed
  | _ + 1, [] => .error .truncated
  | fuel + 1, b :: bs =>
      if b ≥ 256 then .error .malformed
      else if b < 128 then .ok (b, bs)
      else do
        let (high, rest) ← decodeCore fuel bs
        if high = 0 then .error .malformed
        else .ok (b % 128 + 128 * high, rest)

/-- The decoder checks the bound before constructing its proof field. -/
opaque decode? (bs : List Nat) : Except DecodeError (UVarint × List Nat) := do
  let (n, rest) ← decodeCore maxBytes bs
  if h : n < limit then .ok (⟨n, h⟩, rest)
  else .error .malformed

/-- Executable stand-in for W2.1's production decoder and consumed count. -/
opaque decodeB? (bs : ByteArray) : Except DecodeError (UVarint × Nat) := do
  let (v, rest) ← decode? (bs.toList.map UInt8.toNat)
  .ok (v, bs.size - rest.length)

/-- W2.1's suffix roundtrip contract. -/
axiom decodeEncodeSuffix (v : UVarint) (rest : List Nat) :
  decode? (encode v ++ rest) = .ok (v, rest)

/-- W2.1's accepted-input decomposition. -/
axiom encodeDecode (bs : List Nat) (v : UVarint) (rest : List Nat) :
  decode? bs = .ok (v, rest) → bs = encode v ++ rest

/-- An encoded varint always consumes a tag byte. -/
axiom encodeNonempty (v : UVarint) : encode v ≠ []

/-- The production byte model contains only byte-valued entries. -/
axiom encodeBytes (v : UVarint) : ∀ b ∈ encode v, b < 256

end Pb.Mock.Varint
