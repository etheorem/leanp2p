import Tests.Support
import Varint

/-!
# Varint suite (unit W2.1)

The checks of `packages/codec/varint/docs/PLAN.md`, "Test milestones",
and the varint vector suite (`varint-examples.json`, from the
multiformats `unsigned-varint` README).

The theorems of `Varint` prove the round trip and the split on the
model. This suite pins the production decoder to the model through the
generic harness of `base/bytes`, and it checks the wire bytes against
the spec.
-/

set_option autoImplicit false

namespace Tests

open Bytes Varint

/-- A varint for a value inside the budget; `none` outside it. -/
private def uvarint? (n : Nat) : Option UVarint :=
  if h : n < limit then some ⟨n, h⟩ else none

/-- The production decoder in the harness shape. `decodeB?` returns
the consumed count, and the harness compares the model rest, so the
adapter drops the consumed bytes from the model view of the input. -/
private def production (b : ByteArray) : Except DecodeError (UVarint × List Nat) :=
  (decodeB? b).map fun (v, n) => (v, (toNatList b).drop n)

/-- The values at every group-length boundary: `2^(7k) - 1`, the largest
value of `k` bytes, and `2^(7k)`, the smallest of `k + 1`, up to the top
of the budget. -/
private def boundaryValues : List Nat :=
  (List.range 10).flatMap fun k => [2 ^ (7 * k) - 1, 2 ^ (7 * k)]

/-- Seeded values spread over the budget. The multiplier is odd, so the
products stay distinct modulo `2 ^ 63`. -/
private def seededValues : List Nat :=
  (List.range 300).map fun s => (s * 0x9E3779B97F4A7C15 + s * s * s) % 2 ^ 63

/-- Inputs shaped like varint prefixes: `k` continuation bytes, then
each of a set of last bytes, for `k` up to 10. The set holds the zero
terminator, a plain terminator, the largest terminator, and another
continuation. -/
private def prefixInputs : List ByteArray :=
  (List.range 11).flatMap fun k =>
    [0x00, 0x01, 0x7F, 0x80, 0xFF].flatMap fun last =>
      [0x80, 0xFF].map fun cont => ofNatList (List.replicate k cont ++ [last])

/-- Every input of one or two bytes. -/
private def shortInputs : List ByteArray :=
  (List.range 256).map (fun a => ofNatList [a]) ++
    (List.range 65536).map fun n => ofNatList [n / 256, n % 256]

/-- Seeded inputs up to 12 bytes. The upper half of the byte range is
twice as likely, so long continuation runs occur. -/
private def seededInputs : List ByteArray :=
  (List.range 500).map fun s =>
    ofNatList <| (List.range (s % 13)).map fun j =>
      let x := (s * 73 + j * 151 + j * j * 17) % 384
      if x < 256 then x else x - 128

def Varint.run (r : Runner) : IO Unit := do
  r.section "varint" "multiformats/unsigned-varint README.md"

  -- The spec examples, model and wire, both directions.
  let file := "varint-examples.json"
  let j ← loadJson file
  for e in ← jArr file j "examples" do
    let n ← jNat file e "n"
    let hex ← jStr file e "uvarintHex"
    let some v := uvarint? n | r.check s!"{file} n={n} fits the budget" false; continue
    let some wire := ofHex? hex | r.check s!"{file} n={n} hex" false; continue
    r.check s!"{file} n={n}: encodeB" (encodeB v == wire)
    r.check s!"{file} n={n}: encode" (encode v == toNatList wire)
    r.check s!"{file} n={n}: decodeB? reads the value and the length"
      (succeedsWith (v, wire.size) (decodeB? wire))
    r.check s!"{file} n={n}: decode? reads the value"
      (succeedsWith (v, []) (decode? (toNatList wire)))

  -- The recorded counterexample of the minimal rule.
  for rule in ← jArr file j "rules" do
    if let some hex ← jStr? file rule "counterExampleHex" then
      let some wire := ofHex? hex | r.check s!"{file} counterexample hex" false; continue
      r.check s!"{file} counterexample {hex}: decodeB? is malformed"
        (failsWith .malformed (decodeB? wire))
      r.check s!"{file} counterexample {hex}: decode? is malformed"
        (failsWith .malformed (decode? (toNatList wire)))

  -- The package's own table: the spec examples the vector file lacks.
  for (n, bytes) in [(0, [0x00]), (1, [0x01]), (127, [0x7F]), (128, [0x80, 0x01]),
      (300, [0xAC, 0x02])] do
    let some v := uvarint? n | r.check s!"table n={n} fits the budget" false; continue
    r.check s!"table n={n}: encodeB" (encodeB v == ofNatList bytes)
    r.check s!"table n={n}: encode" (encode v == bytes)

  -- The package's own rejections.
  let bad : List (String × List Nat × DecodeError) := [
    ("0x80 0x00, non-minimal zero", [0x80, 0x00], .malformed),
    ("0x81 0x00, non-minimal one", [0x81, 0x00], .malformed),
    ("nine continuation bytes", List.replicate 9 0x80, .malformed),
    ("a 10-byte prefix", List.replicate 9 0x80 ++ [0x01], .malformed),
    ("a lone 0x80", [0x80], .truncated),
    ("eight continuation bytes", List.replicate 8 0x80, .truncated),
    ("the empty input", [], .truncated)]
  for (name, bytes, e) in bad do
    r.check s!"decodeB? of {name} is {repr e}" (failsWith e (decodeB? (ofNatList bytes)))
    r.check s!"decode? of {name} is {repr e}" (failsWith e (decode? bytes))

  -- The top of the budget: 2^63 - 1 takes 9 bytes, and 2^63 is outside.
  r.check "2^63 - 1 fits the budget in 9 bytes"
    ((uvarint? (2 ^ 63 - 1)).any fun v => (encode v).length == 9)
  r.check "2^63 is outside the budget" (uvarint? (2 ^ 63)).isNone

  -- The harness: the round trip at every boundary value and on seeded
  -- values, and the model pin on every input up to two bytes, on every
  -- prefix shape up to 11 bytes, and on seeded inputs up to 12 bytes.
  let values := (boundaryValues ++ seededValues).filterMap uvarint?
  r.check s!"harness round trip over {values.length} values" (checkRoundTrips values)
  r.check s!"harness model pin over {values.length} encodings"
    (checkModelPins production (values.map encodeB))
  let inputs := shortInputs ++ prefixInputs ++ seededInputs
  r.check s!"harness model pin over {inputs.length} inputs" (checkModelPins production inputs)
  r.check "the model pin reports a wrong decoder"
    (!checkModelPins (α := UVarint) (fun _ => .error .malformed) [ofNatList [0x01]])

end Tests
