import Tests.Support
import Multiformats

/-!
# Multiaddr boundary fixtures

These checks exercise protocol values, segmentation and the validated
wire sequence without deciding how a complete address remembers a peer
text spelling. Fixtures are consumed exactly as captured.
-/

set_option autoImplicit false

namespace Tests.MultiaddrWire

open _root_.Multiformats

/-- Complete address acceptance is independent of its printed peer spelling. -/
private def accept (frames : List ComponentWire.Frame) : Bool :=
  frames.all Multiaddr.validFrame && Multiaddr.validOrder frames &&
    (frames.map ComponentWire.encodedLength).sum ≤ maxAddressBytes

/-- The sequence model carries all checked address invariants. -/
private abbrev Address := SequenceWire.Value accept

/-- Text segmentation and value parsing meet at a checked wire sequence. -/
private def parse? (text : String) : Except Error Address := do
  let parts ← Multiaddr.parseSegments? text
  let frames ← parts.mapM Multiaddr.segmentFrame?
  if h : accept frames = true then .ok ⟨frames, h⟩ else .error .badAddress

/-- Canonical wire printing uses the default peer spelling. -/
private def print? (frames : List ComponentWire.Frame) : Except Error String := do
  if frames.isEmpty then .ok "/"
  else
    let parts ← frames.mapM fun frame => do
      let value ← Multiaddr.valueString? frame
      if frame.proto == .unix then .ok ("/unix" ++ value)
      else if frame.proto.fixedBytes? == some 0 then .ok ("/" ++ frame.proto.name)
      else .ok ("/" ++ frame.proto.name ++ "/" ++ value)
    .ok (String.join parts)

/-- The byte boundary checks the whole budget before reading a component. -/
private def decodeB? (input : ByteArray) : Except Error Address := do
  if input.size > maxAddressBytes then .error .overCap
  else
    let (value, used) ← SequenceWire.decodeB? accept input
    if used == input.size then .ok value else .error .badAddress

/-- The pin adapter validates consumption before returning an empty remainder. -/
private def production (input : ByteArray) : Except Bytes.DecodeError (Address × List Nat) := do
  let value ← (decodeB? input).mapError Error.toDecodeError
  .ok (value, [])

/-- Malformed fixture hex fails the test rather than becoming empty input. -/
private def hexBytes (text : String) : IO ByteArray := do
  let digit (c : Char) : IO Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - 48)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 87)
    else throw <| IO.userError s!"bad fixture hex: {c}"
  let rec go : List Char → IO (List Nat)
    | [] => pure []
    | [_] => throw <| IO.userError "odd fixture hex"
    | a :: b :: rest => do pure ((16 * (← digit a) + (← digit b)) :: (← go rest))
  return Bytes.ofNatList (← go text.toList)

/-- Success rows exercise model laws and the independent cursor decoder. -/
private def checkAddress (runner : Runner) (label text : String) : IO Unit := do
  match parse? text with
  | .error e => runner.check s!"{label}: {text}: {repr e}" false
  | .ok address =>
      let bytes := Bytes.ofNatList (SequenceWire.encode address)
      runner.check (label ++ " independent byte encoder") (SequenceWire.encodeFramesB address.frames == bytes)
      runner.check (label ++ " model roundtrip") (Bytes.checkRoundTrips [address])
      runner.check (label ++ " byte/model agreement") (Bytes.checkModelPins production [bytes])
      runner.check (label ++ " canonical text preserves wire bytes")
        (match print? address.frames with
          | .ok printed => match parse? printed with
              | .ok reparsed => reparsed == address
              | .error _ => false
          | .error _ => false)

/-- Captured accepted strings include every supported value family. -/
private def acceptedChecks (runner : Runner) : IO Unit := do
  for file in ["multiaddr-go-construct-succeeds.json", "multiaddr-go-round-trip.json",
      "multiaddr-js-variants.json"] do
    let fixture ← loadJson file
    for row in (← jArr file fixture "cases") do
      if (← jStr? file row "knownDivergence").isSome then
        runner.skip "documented memory text divergence" "the contract uses a big-endian u64"
      else
        let field := if file == "multiaddr-js-variants.json" then "value" else "string"
        checkAddress runner file (← jStr file row field)
  for (file, field) in [("multiaddr-js-construction.json", "addr"),
      ("multiaddr-go-marshaler.json", "addr"), ("multiaddr-go-zone.json", "string")] do
    let fixture ← loadJson file
    checkAddress runner file (← jStr file fixture field)

/-- Literal expected bytes pin encoding separately from roundtrip behavior. -/
private def wireChecks (runner : Runner) : IO Unit := do
  for file in ["multiaddr-go-string-to-bytes.json", "multiaddr-go-bytes-to-string.json"] do
    let fixture ← loadJson file
    for row in (← jArr file fixture "cases") do
      let text ← jStr file row "string"
      let expected ← hexBytes (← jStr file row "bytesHex")
      match parse? text with
      | .error e => runner.check s!"{file}: {repr e}" false
      | .ok address =>
          runner.check "captured text has exact wire bytes"
            (Bytes.ofNatList (SequenceWire.encode address) == expected)
          runner.check "captured bytes have the expected components"
            (match decodeB? expected with | .ok value => value == address | .error _ => false)
          runner.check "captured bytes have the expected text"
            (match decodeB? expected with
              | .ok value => match print? value.frames with | .ok got => got == text | .error _ => false
              | .error _ => false)
  for file in ["multiaddr-go-zone.json", "multiaddr-go-dns.json"] do
    let fixture ← loadJson file
    let bytes ← hexBytes (← jStr file fixture "bytesHex")
    runner.check "zone or DNS bytes match the model" (Bytes.checkModelPins production [bytes])
    runner.check "zone or DNS bytes are accepted"
      (match decodeB? bytes with | .ok _ => true | .error _ => false)

/-- Concrete negative fixtures cover values, ordering, framing and text boundaries. -/
private def invalidChecks (runner : Runner) : IO Unit := do
  for file in ["multiaddr-go-construct-fails.json", "multiaddr-js-invalid.json"] do
    let fixture ← loadJson file
    for row in (← jArr file fixture "cases") do
      let text ← jStr file row "string"
      runner.check ("reject " ++ text)
        (match parse? text with | .error _ => true | .ok _ => false)
  for text in ["tcp/1", "/ip4//x", "/tcp/6_5_5_3_5", "/ip4/010.0.0.1",
      "/ip6zone/eth0", "/ip6zone/eth0/tcp/80", "/ip4/127.0.0.1//tcp/80",
      "/tls//", "/unix/", "/ech/not-multibase"] do
    runner.check ("strict boundary rejects " ++ text)
      (match parse? text with | .error _ => true | .ok _ => false)
  let fixture ← loadJson "multiaddr-go-invalid-p2p.json"
  let bytes ← hexBytes (← jStr "invalid peer bytes" fixture "bytesHex")
  runner.check "binary peer digest mismatch is rejected"
    (match decodeB? bytes with | .error _ => true | .ok _ => false)
  for row in (← jArr "invalid peer strings" fixture "strings") do
    let text ← jStr "invalid peer string" row "string"
    runner.check "invalid peer string is rejected"
      (match parse? text with | .error _ => true | .ok _ => false)
  let path ← loadJson "multiaddr-go-http-path.json"
  let bad ← jStr "HTTP path" path "bad"
  runner.check "HTTP path rejects partial byte escape"
    (match parse? bad with | .error _ => true | .ok _ => false)
  for text in (← jStrs "HTTP paths" path "roundTrip") do
    checkAddress runner "HTTP path" text

/-- Accepted fuzz seeds retain bytes exactly; every seed agrees with the model. -/
private def fuzzChecks (runner : Runner) : IO Unit := do
  let fixture ← loadJson "multiaddr-go-fuzz-bytes.json"
  for hex in (← jStrs "fuzz bytes" fixture "seedsHex") do
    let bytes ← hexBytes hex
    runner.check "captured fuzz bytes model pin" (Bytes.checkModelPins production [bytes])
    match decodeB? bytes with
    | .error _ => pure ()
    | .ok value =>
        runner.check "captured fuzz bytes encode exactly"
          (Bytes.ofNatList (SequenceWire.encode value) == bytes)
        runner.check "captured fuzz bytes print and parse"
          (match print? value.frames with
            | .ok text => match parse? text with | .ok got => got == value | .error _ => false
            | .error _ => false)
  let strings ← loadJson "multiaddr-go-fuzz-strings.json"
  for text in (← jStrs "fuzz strings" strings "seeds") do
    match parse? text with
    | .error _ => pure ()
    | .ok _ => checkAddress runner "captured fuzz string" text
  for seed in List.range 4096 do
    let bytes := Bytes.ofNatList ((List.range (seed % 63)).map fun j =>
      (seed * 127 + j * 79 + j * j * 11) % 256)
    runner.check "generated hostile address model pin" (Bytes.checkModelPins production [bytes])

/-- Non-UTF-8 ECH bytes distinguish decoded data from the input text itself. -/
private def valueChecks (runner : Runner) : IO Unit := do
  for (protocol, text) in [(.ip4, "127.0.0.1"), (.ip6, "::1"), (.tcp, "65535"),
      (.udp, "0"), (.ip6zone, "eth0"), (.ipcidr, "255"), (.dns, "é.example"),
      (.memory, "18446744073709551615"), (.«http-path», "%C3%A9%2Fabc"),
      (.onion, "timaq4ygg2iegci7:80"), (.ech, "u_wCq")] do
    match Multiaddr.parseValue? protocol text with
    | .error e => runner.check s!"value setup {text}: {repr e}" false
    | .ok frame =>
        runner.check "protocol value prints and parses"
          (match Multiaddr.valueString? frame with
            | .ok printed => match Multiaddr.parseValue? protocol printed with
                | .ok got => got == frame
                | .error _ => false
            | .error _ => false)
  runner.check "ECH stores decoded configuration bytes"
    (match Multiaddr.parseValue? .ech "u_wCq" with
      | .ok frame => frame.value == [255, 0, 170]
      | .error _ => false)

/-- Empty operation results are represented by empty component sequences. -/
private def fixtureFrames (text : String) : IO (List ComponentWire.Frame) :=
  if text.isEmpty || text == "/" then pure []
  else match parse? text with
    | .ok value => pure value.frames
    | .error e => throw <| IO.userError s!"operation fixture rejected {text}: {repr e}"

/-- A required protocol name must resolve in the generated table. -/
private def fixtureProtocol (name : String) : IO Protocol :=
  match Protocol.ofName? name with
  | some protocol => pure protocol
  | none => throw <| IO.userError s!"unknown fixture protocol {name}"

/-- Append, suffix removal, equality and split/join use the captured operation cases. -/
private def operationChecks (runner : Runner) : IO Unit := do
  for (file, field) in [("multiaddr-go-decapsulate.json", "cases"),
      ("multiaddr-go-encapsulate.json", "decapsulate")] do
    let fixture ← loadJson file
    for row in (← jArr file fixture field) do
      let left ← fixtureFrames (← jStr file row "left")
      let right ← fixtureFrames (← jStr file row "right")
      let expected ← fixtureFrames ((← jStr? file row "expected").getD "")
      runner.check "Go decapsulate removes last match and tail"
        (SequenceOps.decapsulate? left right == if expected.isEmpty then none else some expected)
  let append ← loadJson "multiaddr-go-encapsulate.json"
  for row in (← jArr "encapsulate" append "encapsulate") do
    let left ← fixtureFrames (← jStr "encapsulate" row "left")
    let right ← fixtureFrames (← jStr "encapsulate" row "right")
    let expected ← fixtureFrames (← jStr "encapsulate" row "expected")
    runner.check "Go encapsulate retains ordered components" (SequenceOps.encapsulate left right == expected)
  for file in ["multiaddr-go-equal.json", "multiaddr-js-equals.json"] do
    let fixture ← loadJson file
    for row in (← jArr file fixture "pairs") do
      let a ← fixtureFrames (← jStr file row "a")
      let b ← fixtureFrames (← jStr file row "b")
      runner.check "captured address equality" ((a == b) == (← jBool file row "equal"))
  let split ← loadJson "multiaddr-go-split.json"
  for row in (← jArr "split" split "cases") do
    let value ← fixtureFrames (← jStr "split" row "addr")
    let expected ← (← jStrs "split" row "parts").mapM fixtureFrames
    runner.check "captured address split" (SequenceOps.split value == expected)
    runner.check "captured parts join in original order" (SequenceOps.join expected == value)
  let js ← loadJson "multiaddr-js-decapsulate.json"
  for row in (← jArr "JS decapsulate" js "cases") do
    let value ← fixtureFrames (← jStr "JS decapsulate" row "addr")
    let sub ← fixtureFrames (← jStr "JS decapsulate" row "sub")
    runner.check "JS absent subaddress is a miss"
      ((SequenceOps.decapsulateThrow? value sub).isSome == (← jBool "JS decapsulate" row "ok"))
  let byCode ← loadJson "multiaddr-js-decapsulate-code.json"
  let tcp ← fixtureFrames (← jStr "relay TCP" byCode "relayTcp")
  let suffix ← fixtureFrames (← jStr "relay suffix" byCode "relaySuffix")
  let target ← fixtureFrames (← jStr "target" byCode "target")
  let code ← jNat "decapsulate code" byCode "code"
  runner.check "decapsulate code removes the last peer component"
    (SequenceOps.decapsulateCode (tcp ++ suffix ++ target) code == tcp ++ suffix)
  runner.check "decapsulate code removes the relay after the target"
    (SequenceOps.decapsulateCode (tcp ++ suffix) code == tcp)

/-- Lookups distinguish an absent protocol from an empty valueless entry. -/
private def viewChecks (runner : Runner) : IO Unit := do
  let fixture ← loadJson "multiaddr-go-get-value.json"
  for row in (← jArr "get value" fixture "cases") do
    let value ← fixtureFrames (← jStr "get value" row "addr")
    for check in (← jArr "get value" row "checks") do
      let protocol ← fixtureProtocol (← jStr "get value" check "proto")
      let expected ← jStr "get value" check "value"
      runner.check "captured first-occurrence value lookup"
        (SequenceOps.valueForProtocol? value protocol.toCode == some expected)
    for name in (← jStrs "missing values" row "missing") do
      let protocol ← fixtureProtocol name
      runner.check "absent protocol is a miss" (SequenceOps.valueForProtocol? value protocol.toCode == none)
  let names ← loadJson "multiaddr-go-protocols-with-string.json"
  for row in (← jArr "protocol names" names "good") do
    let text ← jStr "protocol names" row "addr"
    let expected ← (← jStrs "protocol names" row "protocols").mapM fixtureProtocol
    runner.check "captured protocol-name parser"
      (SequenceOps.protocolsWithString? text == some (expected.map fun p => (p.toCode, p.name)))
  for text in (← jStrs "bad protocol names" names "bad") do
    runner.check "protocol-name parser rejects unknown or empty names"
      (SequenceOps.protocolsWithString? text == none)
  let components ← loadJson "multiaddr-js-get-components.json"
  for row in (← jArr "components" components "cases") do
    if (← jStr? "components" row "knownDivergence").isSome then
      runner.skip "documented memory component divergence" "memory values are big-endian u64"
    else
      let frames ← fixtureFrames (← jStr "components" row "addr")
      let expected ← (← jArr "components" row "components").mapM fun item => do
        let code ← jNat "components" item "code"
        let name ← jStr "components" item "name"
        let value ← jStr? "components" item "value"
        pure (SequenceOps.ComponentView.mk code name value)
      runner.check "captured decoded component view" (SequenceOps.components frames == expected)
  let path ← loadJson "multiaddr-go-http-path.json"
  let valueCase ← jObj "HTTP path value" path "valueCase"
  let frames ← fixtureFrames (← jStr "HTTP path value" valueCase "addr")
  let protocol ← fixtureProtocol (← jStr "HTTP path value" valueCase "proto")
  runner.check "HTTP path lookup remains escaped"
    (SequenceOps.valueForProtocol? frames protocol.toCode == some (← jStr "HTTP path value" valueCase "value"))

/-- Collection operations preserve stable ordering and compare full addresses. -/
private def collectionChecks (runner : Runner) : IO Unit := do
  let fixture ← loadJson "multiaddr-go-unique-addrs.json"
  for row in (← jArr "unique" fixture "tables") do
    let input ← (← jStrs "unique" row "in").mapM fixtureFrames
    let expected ← (← jStrs "unique" row "out").mapM fixtureFrames
    runner.check "captured stable address deduplication" (SequenceOps.unique input == expected)
  let membership ← loadJson "multiaddr-go-contains.json"
  let addresses ← (← jStrs "contains" membership "addrs").mapM fixtureFrames
  for text in (← jStrs "contains" membership "members") do
    runner.check "captured address membership" (SequenceOps.contains addresses (← fixtureFrames text))
  for text in (← jStrs "contains" membership "nonMembers") do
    runner.check "captured address non-membership" (!SequenceOps.contains addresses (← fixtureFrames text))
  let filtered ← loadJson "multiaddr-go-filter-addrs.json"
  let good ← (← jStrs "filter" filtered "good").mapM fixtureFrames
  let bad ← (← jStrs "filter" filtered "bad").mapM fixtureFrames
  runner.check "captured address filter retains order"
    (SequenceOps.filter (good ++ bad) (fun frames => frames.head?.map (·.proto) == some .ip4) == good)
  let aliases ← loadJson "multiaddr-go-ipfs-v-p2p.json"
  let p2p ← fixtureFrames (← jStr "aliases" aliases "p2p")
  let ipfs ← fixtureFrames (← jStr "aliases" aliases "ipfs")
  runner.check "legacy peer name has identical wire identity" (p2p == ipfs)

/-- Run the independent wire boundary while the presentation contract is pending. -/
def run (runner : Runner) : IO Unit := do
  runner.section "multiaddr wire" "captured Go and JavaScript boundary vectors"
  valueChecks runner
  acceptedChecks runner
  wireChecks runner
  invalidChecks runner
  fuzzChecks runner
  operationChecks runner
  viewChecks runner
  collectionChecks runner

end Tests.MultiaddrWire
