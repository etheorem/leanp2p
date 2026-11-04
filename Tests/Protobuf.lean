import Tests.Support
import Proto

/-!
# Protobuf wire tests

The message fixtures run in the Fields view, without importing upper
packages. The suite also pins the independent ByteArray decoder to the
model over valid messages, truncated fixtures, and adversarial buffers.
The shared Bytes harness checks the real codec instance and model pin.
-/

set_option autoImplicit false

namespace Tests.Protobuf

open Pb

/-- Invalid test data is a suite error, not a protocol error to swallow. -/
private def checked (entries : List Entry) : IO Fields :=
  match Fields.ofList? entries with
  | .ok fs => pure fs
  | .error e => throw <| IO.userError s!"invalid protobuf test fields: {repr e}"

/-- A model byte list as a production-path fixture. -/
private def bytes (bs : List Nat) : ByteArray := Bytes.ofNatList bs

/-- Complete messages must consume their whole buffer before the shared model pin. -/
private def production (bs : ByteArray) : Except Bytes.DecodeError (Fields × List Nat) := do
  let (fs, used) ← (decodeFieldsB? bs).mapError Error.toDecodeError
  if used = bs.size then .ok (fs, []) else .error .malformed

/-- The model pin for one arbitrary buffer, valid or hostile. -/
private def pin (bs : ByteArray) : Bool :=
  Bytes.checkModelPins production [bs]

/-- The generic codec harness over one sample. -/
private def roundtrip (fs : Fields) : Bool :=
  Bytes.checkRoundTrips [fs] && pin (encodeFieldsB fs)

/-- The model decoder reports exactly the expected error. -/
private def modelError (input : List Nat) (expected : Error) : Bool :=
  match decodeFields? input with
  | .error e => e == expected
  | .ok _ => false

/-- The production decoder reports exactly the expected error. -/
private def byteError (input : List Nat) (expected : Error) : Bool :=
  match decodeFieldsB? (bytes input) with
  | .error e => e == expected
  | .ok _ => false

/-- Hex parsing is fixture plumbing and rejects malformed fixture text. -/
private def hexBytes (text : String) : IO ByteArray := do
  let digit (c : Char) : IO Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw <| IO.userError s!"invalid hex character: {c}"
  let rec go : List Char → IO (List Nat)
    | [] => pure []
    | [_] => throw <| IO.userError "odd fixture hex length"
    | a :: b :: rest => do
        let hi ← digit a
        let lo ← digit b
        let tail ← go rest
        pure ((16 * hi + lo) :: tail)
  return bytes (← go text.toList)

private def checkFixture (r : Runner) (name : String) (bs : ByteArray) : IO Unit := do
  r.check s!"model pin: {name}" (pin bs)
  match decodeFieldsB? bs with
  | .error e => r.check s!"decode fixture {name}: {repr e}" false
  | .ok (fs, used) =>
      r.check s!"fixture consumed count: {name}" (used == bs.size)
      r.check s!"fixture byte-exact re-encode: {name}" (encodeFieldsB fs == bs)
      r.check s!"generic codec harness: {name}" (roundtrip fs)
  -- A prefix may itself end at a legal field boundary. Compare both
  -- decoders rather than assuming that every prefix must be rejected.
  for n in List.range (min (bs.size + 1) 65) do
    r.check s!"fixture prefix pin: {name}/{n}" (pin (bs.extract 0 n))

/-- A small message table tests the generic API without upper-layer dependencies. -/
private structure Counter where
  value : Fin (2 ^ 63)
  deriving BEq, Repr

private instance : ProtoMessage Counter where
  toFields c := ⟨[(1, .varint c.value.val)], by
    intro e he
    simp only [List.mem_singleton] at he
    subst e
    change 0 < 1 ∧ 1 < 2 ^ 29 ∧ c.value.val < Varint.limit
    exact ⟨by decide, by decide, c.value.isLt⟩⟩
  ofFields? fs :=
    match getVarint? 1 fs with
    | none => .error .badField
    | some n =>
        if h : n < 2 ^ 63 then .ok ⟨⟨n, h⟩⟩ else .error .badField

/-- The theorem can be applied to any bounded message, with no native certificate. -/
example (fs : Fields) : decodeFields? (encodeFields fs) = .ok (fs, []) := decodeEncode fs

/-- Every emitted model entry is a byte. -/
example (fs : Fields) : ∀ b ∈ encodeFields fs, b < 256 := encodeFieldsBytes fs

/-- The public instance participates in the shared byte-codec law. -/
example (fs : Fields) : Bytes.Codec.decode? (Bytes.Codec.encode fs) = .ok (fs, []) :=
  Bytes.codecRoundTrip fs

/-- Encoding through the real ByteArray conversion is lossless. -/
example (fs : Fields) : Bytes.toNatList (encodeFieldsB fs) = encodeFields fs :=
  encodeFieldsBModel fs

/-- The shared inverse law preserves the exact input and its returned remainder. -/
example (input rest : List Nat) (fs : Fields)
    (accepted : Bytes.Codec.decode? input = .ok (fs, rest)) :
    Bytes.Codec.encode fs ++ rest = input :=
  Bytes.LawfulCodec.encodeDecode input fs rest accepted

def run (r : Runner) : IO Unit := do
  r.section "protobuf" "wire model, protobuf-messages.json, keys-peer-ids.json, keys-go-libp2p.json"

  let sample ← checked [(1, .varint 150), (2, .fixed64 0x0102030405060708),
    (3, .bytes [0, 255]), (4, .fixed32 0x01020304)]
  let expected := [0x08, 0x96, 0x01, 0x11, 8, 7, 6, 5, 4, 3, 2, 1,
    0x1a, 2, 0, 255, 0x25, 4, 3, 2, 1]
  r.check "four wire types: fixed model bytes" (encodeFields sample == expected)
  r.check "four wire types: fixed production bytes" (encodeFieldsB sample == bytes expected)
  r.check "four wire types: roundtrip" (roundtrip sample)
  r.check "empty message" (roundtrip Fields.empty)

  let boundary ← checked [(1, .varint (2 ^ 63 - 1)),
    (536870911, .fixed64 (2 ^ 64 - 1)), (2, .fixed32 (2 ^ 32 - 1)), (3, .bytes [])]
  r.check "maximum supported values and empty payload" (roundtrip boundary)

  let many ← checked (List.replicate 2048 (1, .varint 127))
  r.check "many small fields preserve their count and byte offsets" (roundtrip many)

  let duplicate ← checked [(7, .varint 1), (99, .bytes [2, 3]), (7, .varint 9)]
  r.check "last occurrence wins" (getVarint? 7 duplicate == some 9)
  r.check "repeated occurrences preserve order" (getAllVarints 7 duplicate == [1, 9])
  r.check "unknown field survives" (roundtrip duplicate && getBytes? 99 duplicate == some [2, 3])
  r.check "presence and absence" (hasField 99 duplicate && !hasField 100 duplicate)
  let mixed ← checked [(7, .varint 1), (7, .bytes [])]
  r.check "singular lookup checks the last wire type" (getVarint? 7 mixed == none)

  let text ← checked [(2, .bytes [0x68, 0x69]), (2, .bytes [0xff])]
  r.check "invalid last UTF-8 payload has no string reading" (getStr? 2 text == none)
  r.check "repeated UTF-8 readings keep valid occurrences" (getAllStrs 2 text == ["hi"])
  let nested ← checked [(4, .bytes (encodeFields sample))]
  match getSub? 4 nested with
  | .ok (some fs) => r.check "nested message" (fs == sample)
  | _ => r.check "nested message" false
  let invalidNested ← checked [(4, .bytes [0x80])]
  r.check "nested malformed message retains its error"
    (match getSub? 4 invalidNested with | .error (.framing .truncated) => true | _ => false)

  let malformed : List (String × List Nat × Error) := [
    ("cut tag", [0x80], .framing .truncated),
    ("cut varint", [8, 0x80], .framing .truncated),
    ("cut fixed64", [9, 1, 2], .framing .truncated),
    ("cut fixed32", [13, 1, 2], .framing .truncated),
    ("cut length", [10, 0x80], .framing .truncated),
    ("cut payload", [10, 5, 1], .framing .truncated),
    ("start group", [11], .badWireType),
    ("end group", [12], .badWireType),
    ("wire type six", [14], .badWireType),
    ("wire type seven", [15], .badWireType),
    ("zero tag", [0], .badField),
    ("nonminimal tag", [0x88, 0], .framing .malformed),
    ("nonminimal value", [8, 0x80, 0], .framing .malformed),
    ("nonminimal length", [10, 0x80, 0], .framing .malformed),
    ("overlong tag", List.replicate 9 0x80, .framing .malformed),
    ("overlong value", 8 :: List.replicate 9 0x80, .framing .malformed),
    ("overlarge field number", encodeNat (2 ^ 29 * 8), .badField),
    ("huge promised payload", [10] ++ encodeNat (2 ^ 63 - 1), .framing .truncated)]
  for (name, input, expectedError) in malformed do
    r.check s!"model rejection: {name}" (modelError input expectedError)
    r.check s!"production rejection: {name}" (byteError input expectedError)

  for input in [[256], [9, 256], [9, 256, 0, 0, 0, 0, 0, 0, 0],
      [10, 1, 256], [10, 5, 256]] do
    r.check "model rejects non-byte entries" (modelError input (.framing .malformed))
  for entries in [[(0, .varint 1)], [(1, .varint (2 ^ 63))],
      [(1, .fixed64 (2 ^ 64))], [(1, .fixed32 (2 ^ 32))], [(1, .bytes [256])]] do
    r.check "constructor rejects invalid field bounds"
      (match Fields.ofList? entries with | .error _ => true | .ok _ => false)

  let mut samples : List Fields := []
  for i in List.range 256 do
    let payload := (List.range (i % 17)).map fun j => (j * 97 + i) % 256
    let fs ← checked [(1, .varint (i * 8191)), (3, .bytes payload),
      (2, .fixed32 (i * 65537)), (4, .fixed64 (i * 4294967297)), (1, .varint i)]
    samples := fs :: samples
  r.check "shared codec laws: 256 generated bounded messages"
    (Bytes.checkRoundTrips samples)
  r.check "shared production pin: 256 generated bounded messages"
    (Bytes.checkModelPins production (samples.map encodeFieldsB))

  -- All one-byte buffers and deterministic short hostile inputs exercise
  -- wire dispatch, continuation bits, truncation, and arbitrary payloads.
  for i in List.range 256 do
    r.check s!"single-byte model pin {i}" (pin (bytes [i]))
  for seed in List.range 4096 do
    let input := (List.range (seed % 33)).map fun j =>
      (seed * 73 + j * 151 + j * j * 17) % 256
    r.check s!"hostile buffer model pin {seed}" (pin (bytes input))

  let msg : Counter := ⟨⟨150, by decide⟩⟩
  r.check "generic message model API"
    (match (decodeMessage? (encodeMessage msg) : Except Error (Counter × List Nat)) with
      | .ok (got, rest) => got == msg && rest.isEmpty
      | .error _ => false)
  r.check "generic message production API"
    (match (decodeMessageB? (encodeMessageB msg) : Except Error (Counter × Nat)) with
      | .ok (got, used) => got == msg && used == (encodeMessageB msg).size
      | .error _ => false)

  let fixture ← loadJson "protobuf-messages.json"
  for item in (← jArr "protobuf-messages.json" fixture "cases") do
    let name ← jStr "protobuf-messages.json" item "name"
    checkFixture r name (← hexBytes (← jStr "protobuf-messages.json" item "bytesHex"))
  let keys ← loadJson "keys-peer-ids.json"
  for item in (← jArr "keys-peer-ids.json" keys "keys") do
    let name ← jStr "keys-peer-ids.json" item "name"
    checkFixture r name (← hexBytes (← jStr "keys-peer-ids.json" item "bytesHex"))
  let goKeys ← loadJson "keys-go-libp2p.json"
  for item in (← jArr "keys-go-libp2p.json" goKeys "cases") do
    let name ← jStr "keys-go-libp2p.json" item "name"
    for key in ["pubHex", "privHex"] do
      checkFixture r s!"go {name} {key}"
        (← hexBytes (← jStr "keys-go-libp2p.json" item key))

end Tests.Protobuf
