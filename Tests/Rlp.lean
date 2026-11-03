import Tests.Support
import Libp2p.Identity

/-!
# RLP suite (unit W6.1)

The acceptance suite of the package's RLP codec: the ethereum/tests
`RLPTests` vectors (`rlp-valid.json`, `rlp-invalid.json`), the
package's own error-kind cases, and the generic harness of
`base/bytes`. The `LawfulCodec Rlp.Value` instance carries the round
trip and the canonical-form law as theorems; this suite pins the
`ByteArray` decoder to the model and the model to the wire.
-/

set_option autoImplicit false

namespace Tests

open Bytes
open Lean (Json)
open Libp2p.Identity

/-- An item tree of the vector file: `{"bytes": hex}` or
`{"list": [...]}`. The depth argument bounds the recursion; the
vectors nest at most a few levels. -/
private def itemOf (file : String) : Nat → Json → IO Rlp.Item
  | 0, _ => throw <| IO.userError s!"{file}: item nests too deep"
  | d + 1, j => do
    match j.getObjVal? "bytes" with
    | .ok v =>
      let some b := ofHex? (← IO.ofExcept v.getStr?)
        | throw <| IO.userError s!"{file}: bad hex"
      return .bytes (toNatList b)
    | .error _ =>
      let arr ← jArr file j "list"
      return .list (← arr.mapM (itemOf file d))

/-- The production decoder in the harness shape: the consumed count
becomes the model rest. -/
private def production (b : ByteArray) : Except DecodeError (Rlp.Value × List Nat) :=
  (Rlp.decodeB? b).map fun (v, n) => (v, (toNatList b).drop n)

/-- True when the whole input decodes to one value. RLPTests marks an
input invalid when no single item spans it. -/
private def wholeB (b : ByteArray) : Bool :=
  match Rlp.decodeB? b with
  | .ok (_, n) => n == b.size
  | .error _ => false

private def wholeModel (l : List Nat) : Bool :=
  match Rlp.decode? l with
  | .ok (_, rest) => rest.isEmpty
  | .error _ => false

/-- Seeded inputs up to 40 bytes, header bytes twice as likely. -/
private def seededInputs : List ByteArray :=
  (List.range 2000).map fun s =>
    ofNatList <| (List.range (s % 41)).map fun j =>
      let x := (s * 131 + j * 197 + j * j * 23) % 320
      if x < 256 then x else 0x80 + (x - 256)

/-- Every input of one or two bytes. -/
private def shortInputs : List ByteArray :=
  (List.range 256).map (fun a => ofNatList [a]) ++
    (List.range 65536).map fun n => ofNatList [n / 256, n % 256]

def Rlp.run (r : Runner) : IO Unit := do
  r.section "rlp" "ethereum/tests RLPTests/rlptest.json, RLPTests/invalidRLPTest.json"

  -- The valid vectors: the encoding, both decoders, and the round trip.
  let file := "rlp-valid.json"
  let j ← loadJson file
  let mut values : List Rlp.Value := []
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    let item ← itemOf file 16 (← jObj file c "item")
    let some wire := ofHex? (← jStr file c "outHex") | r.check s!"{file} {name}: hex" false; continue
    if h : item.valid = true then
      let v : Rlp.Value := ⟨item, h⟩
      values := v :: values
      r.check s!"{file} {name}: encode" (Rlp.encode item == toNatList wire)
      r.check s!"{file} {name}: encodeB" (Rlp.encodeB v == wire)
      r.check s!"{file} {name}: decode? reads the value"
        (succeedsWith (v, []) (Rlp.decode? (toNatList wire)))
      r.check s!"{file} {name}: decodeB? reads the value and the length"
        (succeedsWith (v, wire.size) (Rlp.decodeB? wire))
    else
      r.check s!"{file} {name}: the item is valid" false

  -- The invalid vectors: no single item spans the input.
  let file := "rlp-invalid.json"
  let j ← loadJson file
  let mut invalid : List ByteArray := []
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    let some wire := ofHex? (← jStr file c "inHex") | r.check s!"{file} {name}: hex" false; continue
    invalid := wire :: invalid
    r.check s!"{file} {name}: decodeB? refuses it" (!wholeB wire)
    r.check s!"{file} {name}: decode? refuses it" (!wholeModel (toNatList wire))

  -- The package's own cases: each rule, with its error kind.
  let cases : List (String × List Nat × DecodeError) := [
    ("the empty input", [], .truncated),
    ("0x81 0x00: a byte below 0x80 in a header", [0x81, 0x00], .malformed),
    ("0x81 0x7f", [0x81, 0x7f], .malformed),
    ("0xb8 0x37: a long length below 56", [0xb8, 0x37] ++ List.replicate 55 0x61, .malformed),
    ("0xb9 0x00 0x38: a long length with a leading zero", [0xb9, 0x00, 0x38], .malformed),
    ("0xf8 0x01 0x80: a long list length below 56", [0xf8, 0x01, 0x80], .malformed),
    ("0x83 0x61: a string short of its length", [0x83, 0x61], .truncated),
    ("0xb8: the length bytes missing", [0xb8], .truncated),
    ("0xc2 0x83 0x61: an element crossing the end of its list",
      [0xc2, 0x83, 0x61, 0x62, 0x63], .malformed),
    ("0xc1: a list short of its payload", [0xc1], .truncated)]
  for (name, bytes, e) in cases do
    r.check s!"decode? of {name} is {repr e}" (failsWith e (Rlp.decode? bytes))
    r.check s!"decodeB? of {name} is {repr e}" (failsWith e (Rlp.decodeB? (ofNatList bytes)))

  -- A value in the model that is not a byte is not valid, so the
  -- model decoder refuses it.
  r.check "decode? refuses a model value of 256" (failsWith .malformed (Rlp.decode? [256]))

  -- The scalars of EIP-778: canonical, and bounded.
  r.check "scalar? of [] is 0" (Rlp.scalar? 8 [] == some 0)
  r.check "scalar? of [0x00] is none: a leading zero" (Rlp.scalar? 8 [0x00] == none)
  r.check "scalar? of 9 bytes is none at width 8" (Rlp.scalar? 8 (List.replicate 9 1) == none)
  r.check "ofScalar 30303 is 0x76 0x5f" (Rlp.ofScalar 30303 == [0x76, 0x5f])

  -- The harness: the round trip over the vector values, and the model
  -- pin over the vectors, every input up to two bytes, and seeded inputs.
  r.check s!"harness round trip over {values.length} values" (checkRoundTrips values)
  let inputs := values.map Rlp.encodeB ++ invalid ++ shortInputs ++ seededInputs
  r.check s!"harness model pin over {inputs.length} inputs" (checkModelPins production inputs)
  r.check "the model pin reports a wrong decoder"
    (!checkModelPins (α := Rlp.Value) (fun _ => .error .malformed) [ofNatList [0x01]])

end Tests
