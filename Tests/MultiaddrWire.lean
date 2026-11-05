import Tests.Support
import Multiformats

/-!
# Multiaddr boundary fixtures

These checks exercise the public address API, canonical wire identity,
and the text view that keeps CID-form peer spelling. Fixtures are
consumed exactly as captured.
-/

set_option autoImplicit false

namespace Tests.MultiaddrWire

open _root_.Multiformats

open Multiaddr (parse?)

/-- The pin adapter validates consumption before returning an empty remainder. -/
private def production (input : ByteArray) : Except Bytes.DecodeError (Multiaddr × List Nat) := do
  let value ← (Multiaddr.ofByteArray? input).mapError Error.toDecodeError
  .ok (value, [])

/-- Success rows exercise model laws and the independent cursor decoder. -/
private def checkAddress (runner : Runner) (label text : String) : IO Unit := do
  match parse? text with
  | .error e => runner.check s!"{label}: {text}: {repr e}" false
  | .ok address =>
      let bytes := Bytes.ofNatList address.toBytes
      runner.check (label ++ " independent byte encoder") (address.toByteArray == bytes)
      runner.check (label ++ " model roundtrip") (Bytes.checkRoundTrips [address])
      runner.check (label ++ " byte/model agreement") (Bytes.checkModelPins production [bytes])
      runner.check (label ++ " canonical text preserves wire bytes")
        ((parse? address.toString).toOption == some address)
      runner.check (label ++ " JSON roundtrip")
        ((Multiaddr.ofJSON? address.toJSON).toOption == some address)

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
      let expected ← unhex file (← jStr file row "bytesHex")
      match parse? text with
      | .error e => runner.check s!"{file}: {repr e}" false
      | .ok address =>
          runner.check "captured text has exact wire bytes"
            (Bytes.ofNatList (Multiaddr.encode address) == expected)
          runner.check "captured bytes have the expected components"
            (match Multiaddr.ofByteArray? expected with | .ok value => value == address | .error _ => false)
          runner.check "captured bytes have the expected text"
            (match Multiaddr.ofByteArray? expected with
              | .ok value => value.toString == text
              | .error _ => false)
  for file in ["multiaddr-go-zone.json", "multiaddr-go-dns.json"] do
    let fixture ← loadJson file
    let bytes ← unhex file (← jStr file fixture "bytesHex")
    runner.check "zone or DNS bytes match the model" (Bytes.checkModelPins production [bytes])
    runner.check "zone or DNS bytes are accepted"
      (match Multiaddr.ofByteArray? bytes with | .ok _ => true | .error _ => false)

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
  let bytes ← unhex "invalid peer bytes" (← jStr "invalid peer bytes" fixture "bytesHex")
  runner.check "binary peer digest mismatch is rejected"
    (match Multiaddr.ofByteArray? bytes with | .error _ => true | .ok _ => false)
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
    let bytes ← unhex "fuzz bytes" hex
    runner.check "captured fuzz bytes model pin" (Bytes.checkModelPins production [bytes])
    match Multiaddr.ofByteArray? bytes with
    | .error _ => pure ()
    | .ok value =>
        runner.check "captured fuzz bytes encode exactly"
          (Bytes.ofNatList (Multiaddr.encode value) == bytes)
        runner.check "captured fuzz bytes print and parse"
          (value.frames.isEmpty || (parse? value.toString).toOption == some value)
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
private def fixtureAddress (text : String) : IO Multiaddr :=
  if text.isEmpty || text == "/" then pure Multiaddr.empty
  else match parse? text with
    | .ok value => pure value
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
      let left ← fixtureAddress (← jStr file row "left")
      let right ← fixtureAddress (← jStr file row "right")
      let expected ← fixtureAddress ((← jStr? file row "expected").getD "")
      runner.check "Go decapsulate removes last match and tail"
        ((Multiaddr.decapsulate? left right).toOption == some (if expected.frames.isEmpty then none else some expected))
  let append ← loadJson "multiaddr-go-encapsulate.json"
  for row in (← jArr "encapsulate" append "encapsulate") do
    let left ← fixtureAddress (← jStr "encapsulate" row "left")
    let right ← fixtureAddress (← jStr "encapsulate" row "right")
    let expected ← fixtureAddress (← jStr "encapsulate" row "expected")
    runner.check "Go encapsulate retains ordered components" ((Multiaddr.encapsulate left right).toOption == some expected)
  for file in ["multiaddr-go-equal.json", "multiaddr-js-equals.json"] do
    let fixture ← loadJson file
    for row in (← jArr file fixture "pairs") do
      let a ← fixtureAddress (← jStr file row "a")
      let b ← fixtureAddress (← jStr file row "b")
      runner.check "captured address equality" ((a == b) == (← jBool file row "equal"))
  let split ← loadJson "multiaddr-go-split.json"
  for row in (← jArr "split" split "cases") do
    let value ← fixtureAddress (← jStr "split" row "addr")
    let expected ← (← jStrs "split" row "parts").mapM fixtureAddress
    runner.check "captured address split" ((Multiaddr.split value).toOption == some expected)
    runner.check "captured parts join in original order" ((Multiaddr.join expected).toOption == some value)
  let js ← loadJson "multiaddr-js-decapsulate.json"
  for row in (← jArr "JS decapsulate" js "cases") do
    let value ← fixtureAddress (← jStr "JS decapsulate" row "addr")
    let sub ← fixtureAddress (← jStr "JS decapsulate" row "sub")
    runner.check "JS absent subaddress is a miss"
      (((Multiaddr.decapsulateThrow? value sub).toOption.bind id).isSome == (← jBool "JS decapsulate" row "ok"))
  let byCode ← loadJson "multiaddr-js-decapsulate-code.json"
  let tcp ← fixtureAddress (← jStr "relay TCP" byCode "relayTcp")
  let suffix ← fixtureAddress (← jStr "relay suffix" byCode "relaySuffix")
  let target ← fixtureAddress (← jStr "target" byCode "target")
  let code ← jNat "decapsulate code" byCode "code"
  runner.check "decapsulate code removes the last peer component"
    ((do Multiaddr.decapsulateCode (← Multiaddr.join [tcp, suffix, target]) code).toOption == (Multiaddr.join [tcp, suffix]).toOption)
  runner.check "decapsulate code removes the relay after the target"
    ((do Multiaddr.decapsulateCode (← Multiaddr.join [tcp, suffix]) code).toOption == some tcp)

/-- Lookups distinguish an absent protocol from an empty valueless entry. -/
private def viewChecks (runner : Runner) : IO Unit := do
  let fixture ← loadJson "multiaddr-go-get-value.json"
  for row in (← jArr "get value" fixture "cases") do
    let value ← fixtureAddress (← jStr "get value" row "addr")
    for check in (← jArr "get value" row "checks") do
      let protocol ← fixtureProtocol (← jStr "get value" check "proto")
      let expected ← jStr "get value" check "value"
      runner.check "captured first-occurrence value lookup"
        (Multiaddr.valueForProtocol? value protocol.toCode == some expected)
    for name in (← jStrs "missing values" row "missing") do
      let protocol ← fixtureProtocol name
      runner.check "absent protocol is a miss" (Multiaddr.valueForProtocol? value protocol.toCode == none)
  let names ← loadJson "multiaddr-go-protocols-with-string.json"
  for row in (← jArr "protocol names" names "good") do
    let text ← jStr "protocol names" row "addr"
    let expected ← (← jStrs "protocol names" row "protocols").mapM fixtureProtocol
    runner.check "captured protocol-name parser"
      (Multiaddr.protocolsWithString? text == some (expected.map fun p => (p.toCode, p.name)))
  for text in (← jStrs "bad protocol names" names "bad") do
    runner.check "protocol-name parser rejects unknown or empty names"
      (Multiaddr.protocolsWithString? text == none)
  let components ← loadJson "multiaddr-js-get-components.json"
  for row in (← jArr "components" components "cases") do
    if (← jStr? "components" row "knownDivergence").isSome then
      runner.skip "documented memory component divergence" "memory values are big-endian u64"
    else
      let frames ← fixtureAddress (← jStr "components" row "addr")
      let expected ← (← jArr "components" row "components").mapM fun item => do
        let code ← jNat "components" item "code"
        let name ← jStr "components" item "name"
        let value ← jStr? "components" item "value"
        pure (SequenceOps.ComponentView.mk code name value)
      runner.check "captured decoded component view" (Multiaddr.getComponents frames == expected)
  let path ← loadJson "multiaddr-go-http-path.json"
  let valueCase ← jObj "HTTP path value" path "valueCase"
  let frames ← fixtureAddress (← jStr "HTTP path value" valueCase "addr")
  let protocol ← fixtureProtocol (← jStr "HTTP path value" valueCase "proto")
  runner.check "HTTP path lookup remains escaped"
    (Multiaddr.valueForProtocol? frames protocol.toCode == some (← jStr "HTTP path value" valueCase "value"))

/-- Collection operations preserve stable ordering and compare full addresses. -/
private def collectionChecks (runner : Runner) : IO Unit := do
  let fixture ← loadJson "multiaddr-go-unique-addrs.json"
  for row in (← jArr "unique" fixture "tables") do
    let input ← (← jStrs "unique" row "in").mapM fixtureAddress
    let expected ← (← jStrs "unique" row "out").mapM fixtureAddress
    runner.check "captured stable address deduplication" (Multiaddr.unique input == expected)
  let membership ← loadJson "multiaddr-go-contains.json"
  let addresses ← (← jStrs "contains" membership "addrs").mapM fixtureAddress
  for text in (← jStrs "contains" membership "members") do
    runner.check "captured address membership" (Multiaddr.contains addresses (← fixtureAddress text))
  for text in (← jStrs "contains" membership "nonMembers") do
    runner.check "captured address non-membership" (!Multiaddr.contains addresses (← fixtureAddress text))
  let filtered ← loadJson "multiaddr-go-filter-addrs.json"
  let good ← (← jStrs "filter" filtered "good").mapM fixtureAddress
  let bad ← (← jStrs "filter" filtered "bad").mapM fixtureAddress
  runner.check "captured address filter retains order"
    (Multiaddr.filter (good ++ bad) (fun address => address.components.head?.map (·.proto) == some .ip4) == good)
  let aliases ← loadJson "multiaddr-go-ipfs-v-p2p.json"
  let p2p ← fixtureAddress (← jStr "aliases" aliases "p2p")
  let ipfs ← fixtureAddress (← jStr "aliases" aliases "ipfs")
  runner.check "legacy peer name has identical wire identity" (p2p == ipfs)

/-- The public text view retains CID-form peers while normalizing protocol names and IPs. -/
private def textChecks (runner : Runner) : IO Unit := do
  let normalize ← loadJson "multiaddr-js-normalize.json"
  for row in (← jArr "normalize" normalize "cases") do
    let input ← jStr "normalize" row "input"
    let expected ← jStr "normalize" row "output"
    runner.check ("captured normalization: " ++ input)
      ((Multiaddr.parseText? input).toOption.map Multiaddr.Text.toString == some expected)
  let variants ← loadJson "multiaddr-js-variants.json"
  for row in (← jArr "variants" variants "cases") do
    if (← jStr? "variants" row "knownDivergence").isNone then
      let input ← jStr "variants" row "value"
      let expected := input.replace "/ipfs/" "/p2p/"
      runner.check ("captured text variant: " ++ input)
        ((Multiaddr.parseText? input).toOption.map Multiaddr.Text.toString == some expected)
  let cidText := "/p2p/bafzbeidt255unskpefjmqb2rc27vjuyxopkxgaylxij6pw35hhys4vnyp4"
  match Multiaddr.parseText? cidText with
  | .error e => runner.check s!"peer text setup: {repr e}" false
  | .ok view =>
      runner.check "CID peer text is preserved by the text view" (view.toString == cidText)
      runner.check "canonical text uses the bare peer id" (view.address.toString != cidText)
      runner.check "both peer spellings have identical canonical identity"
        ((parse? view.address.toString).toOption == some view.address)
      runner.check "peer presentation does not affect exact binary roundtrip"
        (Bytes.checkRoundTrips [view.address] &&
          (Multiaddr.ofByteArray? view.address.toByteArray).toOption == some view.address)
  runner.check "empty binary address roundtrips exactly"
    (Bytes.checkRoundTrips [Multiaddr.empty] &&
      (Multiaddr.ofByteArray? ByteArray.empty).toOption == some Multiaddr.empty)
  runner.check "empty binary address has the documented display form" (Multiaddr.empty.toString == "/")
  runner.check "empty display is not accepted as address text" ((parse? "/").toOption.isNone)
  for text in ["/unix/a\"b\\c", "/dns/é.example/tcp/80", "/ip6/::1/tcp/65535"] do
    let address ← fixtureAddress text
    runner.check "JSON escaping preserves the canonical address"
      ((Multiaddr.ofJSON? address.toJSON).toOption == some address)
    runner.check "diagnostics use the canonical printer" (address.describe == toString address)
    runner.check "checked component constructor preserves the canonical address"
      (Multiaddr.ofComponents? address.components == some address)
    runner.check "canonical identity has stable hash and ordering"
      ((Multiaddr.ofComponents? address.components).map hash == some (hash address) &&
        compare address address == .eq)
  for json in ["null", "123", "[]", "{}", "\"tcp/80\"", "\"/tcp/80"] do
    runner.check "JSON rejects non-address input" ((Multiaddr.ofJSON? json).toOption.isNone)

/-- Checked operations cannot construct an address that the decoder would reject. -/
private def constructionChecks (runner : Runner) : IO Unit := do
  let unix ← fixtureAddress "/unix/tmp/socket"
  let tcp ← fixtureAddress "/tcp/80"
  runner.check "append rejects a component after a Unix path"
    ((Multiaddr.encapsulate unix tcp).toOption.isNone)
  runner.check "join validates terminal paths"
    ((Multiaddr.join [unix, tcp]).toOption.isNone)
  let zoned ← fixtureAddress "/ip6zone/eth0/ip6/fe80::1/tcp/80"
  runner.check "split rejects an isolated zone" ((Multiaddr.split zoned).toOption.isNone)
  runner.check "truncation rejects a zone without its IPv6 address"
    ((Multiaddr.decapsulateCode zoned Protocol.ip6.toCode).toOption.isNone)
  let ip6 ← fixtureAddress "/ip6/fe80::1"
  runner.check "suffix removal validates the retained prefix"
    ((Multiaddr.decapsulate? zoned ip6).toOption.isNone)
  for component in [Component.mk .ip4 [127, 0, 0], .mk .tcp [0, 256],
      .mk .dns [], .mk .dns [255], .mk .ip6zone [120], .mk .tls [0]] do
    runner.check "raw component construction checks width, bytes, semantics and order"
      ((Multiaddr.ofComponents? [component]).isNone)
  let payload := List.replicate (maxComponentBytes - 1) 97
  match Multiaddr.fromComponents? (List.replicate 8 (.mk .dns payload)) with
  | .error e => runner.check s!"address budget setup: {repr e}" false
  | .ok large =>
      runner.check "append rejects a combined address over the complete budget"
        ((Multiaddr.encapsulate large large).toOption.isNone)
      runner.check "join rejects a combined address over the complete budget"
        ((Multiaddr.join [large, large]).toOption.isNone)
  let hostile := Bytes.ofNatList (List.replicate (maxAddressBytes + 1) 0)
  runner.check "production decoder rejects the whole-address cap before parsing"
    (match Multiaddr.ofByteArray? hostile with | .error .overCap => true | _ => false)
  runner.check "model decoder rejects the same whole-address cap"
    (match Multiaddr.ofBytes? (Bytes.toNatList hostile) with | .error .overCap => true | _ => false)
  let json := String.ofList (List.replicate (maxAddressJsonBytes + 1) ' ')
  runner.check "JSON checks its escaped-text budget before parsing"
    (match Multiaddr.ofJSON? json with | .error .overCap => true | _ => false)
  match Multiaddr.fromComponents? (List.replicate 270000 (.mk .tls [])) with
  | .error e => runner.check s!"long address setup: {repr e}" false
  | .ok address =>
      let bytes := address.toByteArray
      runner.check "long repeated-protocol address pins the cursor reader to the model"
        (Bytes.checkModelPins production [bytes])
      runner.check "long repeated-protocol address encodes independently"
        (Bytes.ofNatList address.toBytes == bytes)
      runner.check "expanded display has its own text input budget"
        (address.toString.utf8ByteSize > maxAddressBytes &&
          (match parse? address.toString with | .error .overCap => true | _ => false))

/-- Run the public API against the independent wire and text fixtures. -/
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
  textChecks runner
  constructionChecks runner

end Tests.MultiaddrWire
