import Streams.Mock.Bytes

/-!
# Mock: the surface of `codec/varint`

W2.1 (`codec/varint`) is still open, so this package builds against
a mock of its surface (RULES.md, "Working ahead of the tree";
ARCHITECTURE §4.3). The mock imports nothing from `Varint`. When W2.1
merges, the package drops this module, and each `open` of
`Streams.Mock.Varint` becomes an `open` of `Varint`.

The forms follow `Streams.Mock.Bytes`. `maxBytes`, `limit`, the
`UVarint` newtype, and `encode` are copies, since the frame proofs
compute with them. The model functions and the `ByteArray` decoder are
`opaque`, with bodies, so the tests run real varints and no proof can
unfold them. The names follow the open W2.1 pull request,
etheorem/leanp2p#34.

## The mock axioms

The framing proofs need two facts about the varint. Each one is an
axiom here, and each one is a theorem of W2.1, with the same name and
statement:

* `decodeEncodeSuffix`: the decode of an encoding, with any rest after
  it.
* `encodeDecode`: a successful decode consumed exactly the encoding of
  its value, and the rest is the input after it.

`#print axioms` in the pull request lists them. The package deletes
them with the mock.
-/

set_option autoImplicit false

namespace Streams.Mock.Varint

open Streams.Mock.Bytes

/-- The byte budget of a varint: at most 9 bytes, so 63 bits. -/
def maxBytes : Nat := 9

/-- The first value outside the budget. -/
def limit : Nat := 2 ^ (7 * maxBytes)

/-- A varint value: a `Nat` inside the 63 bits that 9 bytes carry. -/
structure UVarint where
  /-- The value. -/
  val : Nat
  /-- The value fits the 9-byte budget. -/
  isLt : val < limit
  deriving DecidableEq, Repr

/-- The body of `encodeNat`: a continuation byte per 7-bit group while
more than 7 bits remain, then the final group. -/
private def encodeNatBody (n : Nat) : List Nat :=
  if n < 128 then [n] else (n % 128 + 128) :: encodeNatBody (n / 128)
termination_by n
decreasing_by omega

/-- The encoding of a `Nat` over the byte model. -/
opaque encodeNat (n : Nat) : List Nat :=
  encodeNatBody n

/-- The encoding of a varint over the byte model. -/
def encode (v : UVarint) : List Nat :=
  encodeNat v.val

/-- The body of `decode?`: the groups from byte `i` on, with the rest of
the input. A zero terminator after a continuation is `malformed`, and so
is a ninth byte that continues. -/
private def decodeGroups (i : Nat) : List Nat → Except DecodeError (Nat × List Nat)
  | [] => .error .truncated
  | b :: rest =>
    if 256 ≤ b then .error .malformed
    else if b < 128 then
      if b = 0 ∧ 0 < i then .error .malformed else .ok (b, rest)
    else if maxBytes ≤ i + 1 then .error .malformed
    else (decodeGroups (i + 1) rest).map fun (v, r) => (b - 128 + 128 * v, r)

/-- One varint from the front of the input, and the rest. -/
opaque decode? (l : List Nat) : Except DecodeError (UVarint × List Nat) :=
  match decodeGroups 0 l with
  | .error e => .error e
  | .ok (n, rest) => if h : n < limit then .ok (⟨n, h⟩, rest) else .error .malformed

/-- The body of `decodeB?`: byte `i` on, with `acc` the value of the
groups before it. -/
private def decodeBFrom (b : ByteArray) (i acc : Nat) : Except DecodeError (UVarint × Nat) :=
  if h : i < b.size then
    let byte := b[i].toNat
    if byte < 128 then
      if byte = 0 ∧ 0 < i then .error .malformed
      else
        let v := acc + byte * 128 ^ i
        if hv : v < limit then .ok (⟨v, hv⟩, i + 1) else .error .malformed
    else if i + 1 < maxBytes then decodeBFrom b (i + 1) (acc + (byte - 128) * 128 ^ i)
    else .error .malformed
  else .error .truncated
termination_by maxBytes - i

/-- One varint from the front of `b`, and the number of bytes it took. -/
opaque decodeB? (b : ByteArray) : Except DecodeError (UVarint × Nat) :=
  decodeBFrom b 0 0

instance : Codec UVarint where
  encode := encode
  decode? := decode?

/-- Mock axiom, a theorem of W2.1: the decode of an encoding, with any
rest after it. -/
axiom decodeEncodeSuffix (v : UVarint) (rest : List Nat) :
    decode? (encode v ++ rest) = .ok (v, rest)

/-- Mock axiom, a theorem of W2.1: a successful decode consumed exactly
the encoding of its value. -/
axiom encodeDecode {bs rest : List Nat} {v : UVarint}
    (h : decode? bs = .ok (v, rest)) : bs = encode v ++ rest

instance : LawfulCodec UVarint where
  decodeEncode v := by
    -- `Codec.encode` and `Codec.decode?` unfold to the module functions.
    show decode? (encode v) = _
    simpa using decodeEncodeSuffix v []
  encodeDecode _ _ _ h := (encodeDecode h).symm

end Streams.Mock.Varint
