import Tests.Support
import Multiformats

/-!
# Multiformats conformance

The suite uses the pinned registry inputs and published wire fixtures.
Generated values exercise the lawful model, and arbitrary byte buffers
pin the independent cursor decoder to it.
-/

set_option autoImplicit false

namespace Tests.Multiformats

open _root_.Multiformats

/-- Bad generated test data is a suite failure, independent of decoder behavior. -/
private def hashValue (code : HashCode) (digest : List Nat) : IO Multihash :=
  match Multihash.ofDigest? code digest with
  | .ok value => pure value
  | .error e => throw <| IO.userError s!"invalid generated multihash: {repr e}"

/-- The standalone byte decoder checks consumption before supplying the empty remainder. -/
private def hashProduction (input : ByteArray) :
    Except Bytes.DecodeError (Multihash × List Nat) := do
  let value ← (Multihash.ofByteArray? input).mapError Error.toDecodeError
  .ok (value, [])

/-- Rejection tests keep the detailed wire error visible in both paths. -/
private def hashError (input : List Nat) (expected : Error) : Bool :=
  let model := match Multihash.decode? input with
    | .error e => e == expected
    | .ok _ => false
  let production := match Multihash.ofByteArray? (Bytes.ofNatList input) with
    | .error e => e == expected
    | .ok _ => false
  model && production

/-- Examples apply the model proofs without compiler-generated certificates. -/
example (value : Multihash) : Multihash.decode? (Multihash.encode value) = .ok (value, []) :=
  Multihash.decodeEncode value

example (value : Multihash) : ∀ b ∈ Multihash.encode value, b < 256 :=
  Multihash.encodeBytes value

/-- The generator reads the pinned CSVs again and compares the complete source. -/
private def registryChecks (runner : Runner) : IO Unit := do
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", "scripts/gen-multiformats.lean", "--check"] }
  if result.exitCode != 0 then IO.eprintln (result.stdout ++ result.stderr)
  runner.check "generated source matches all pinned registry inputs" (result.exitCode == 0)
  runner.check "protocol aliases have one canonical wire member"
    (Protocol.ofName? "ipfs" == Protocol.ofName? "p2p")
  runner.check "memory has the documented eight-byte wire width"
    (Protocol.fixedBytes? .memory == some 8 && Protocol.declaredBits? .memory == none)
  runner.check "reserved base prefixes have no encoding"
    ([0, 49, 81, 47].all fun code => (Multibase.Base.ofCode? code).isNone)
  runner.check "emoji alphabet has exactly 256 distinct Unicode scalars"
    (Multibase.emojiAlphabet.length == 256 && Multibase.emojiAlphabet.eraseDups.length == 256)
  let protocols ← loadJson "multiaddr-protocols.json"
  for row in (← jArr "protocol table" protocols "protocols") do
    let code ← jNat "protocol table" row "code"
    let name ← jStr "protocol table" row "name"
    runner.check "captured protocol row agrees with generated registry"
      (match Protocol.ofName? name with | some p => p.toCode == code | none => false)

/-- Base58 leading zeros are data, including an all-zero payload. -/
private def base58Checks (runner : Runner) : IO Unit := do
  for (input, expected) in [([], ""), ([0], "1"), ([0, 0], "11"),
      ([0, 0, 1], "112"), ([0x61], "2g"), ([0x62, 0x62, 0x62], "a3gV")] do
    let bytes := Bytes.ofNatList input
    runner.check "base58 fixed encode bytes" (Base58.encode bytes == expected)
    runner.check "base58 fixed decode bytes"
      (match Base58.decode? expected with | .ok got => got == bytes | .error _ => false)
  for text in ["0", "O", "I", "l", " abc", "abc\n"] do
    runner.check "base58 rejects non-alphabet characters"
      (match Base58.decode? text with | .error _ => true | .ok _ => false)
  for seed in List.range 128 do
    let input := Bytes.ofNatList ((List.range (seed % 40)).map fun j => (seed + j * 97) % 256)
    for (encoded, decoded) in [(Base58.encode input, Base58.decode?),
        (Base58.encodeFlickr input, Base58.decodeFlickr?)] do
      runner.check "base58 generated roundtrip"
        (match decoded encoded with | .ok got => got == input | .error _ => false)

/-- One README label uses a historical dash absent from the registry name. -/
private def baseNamed? (name : String) : Option Multibase.Base :=
  let canonical := if name == "base32pad-upper" then "base32padupper" else name
  Multibase.Base.all.find? (·.name == canonical)

/-- All captured base rows run, including Unicode prefixes and mixed-case digits. -/
private def multibaseChecks (runner : Runner) : IO Unit := do
  for file in ["multibase-basic.json", "multibase-leading-zero.json",
      "multibase-two-leading-zeros.json", "multibase-case-insensitivity.json"] do
    let fixture ← loadJson file
    let input := Bytes.ofString (← jStr file fixture "input")
    for item in (← jArr file fixture "cases") do
      let name ← jStr file item "encoding"
      let expected ← jStr file item "expected"
      match baseNamed? name with
      | none => runner.check s!"unhandled captured multibase row: {name}" false
      | some base =>
          if file != "multibase-case-insensitivity.json" then
            runner.check s!"captured multibase encode: {name}"
              (match Multibase.encode? base input with
                | .ok got => got == expected | .error _ => false)
          runner.check s!"captured multibase decode: {name}"
            (match Multibase.decode? expected with
              | .ok (gotBase, got) => gotBase == base && got == input
              | .error _ => false)
  for (input, expected) in [([65, 66], "RBB8"), ([72, 101, 108, 108, 111, 33, 33], "R%69 VD92EX0"),
      ([98, 97, 115, 101, 45, 52, 53], "RUJCLQE7W581")] do
    let data := Bytes.ofNatList input
    runner.check "RFC 9285 exact encoding"
      (match Multibase.encode? .base45 data with | .ok got => got == expected | .error _ => false)
    runner.check "RFC 9285 exact decoding"
      (match Multibase.decode? expected with | .ok (_, got) => got == data | .error _ => false)
  runner.check "pinned Proquint example"
    (match Multibase.encode? .proquint (Bytes.ofNatList [127, 0, 0, 1]) with
      | .ok got => got == "pro-lusab-babad" | .error _ => false)
  runner.check "Proquint rejects an incomplete sixteen-bit word"
    (match Multibase.encode? .proquint (Bytes.ofNatList [1]) with
      | .error .badBaseValue => true | _ => false)
  for text in ["?abc", "", "fabc", "f0g", "mA", "mAA=", "mAB", "RA", "R:::",
      "R::", "pro-baba", "p-babab", "pro-babab-", "b1n1"] do
    runner.check "multibase malformed text"
      (match Multibase.decode? text with | .error _ => true | .ok _ => false)
  for seed in List.range 128 do
    let data := Bytes.ofNatList ((List.range (seed % 35)).map fun j => (seed + j * 89) % 256)
    for base in Multibase.Base.all do
      let result := Multibase.encode? base data
      if base == .proquint && data.size % 2 != 0 then
        runner.check "Proquint odd-byte domain check"
          (match result with | .error .badBaseValue => true | _ => false)
      else
        runner.check "registered multibase generated roundtrip"
          (match result with
            | .error _ => false
            | .ok encoded => match Multibase.decode? encoded with
              | .ok (gotBase, got) => gotBase == base && got == data
              | .error _ => false)

/-- Captured digest bytes exercise framing without importing a hash implementation. -/
private def hashChecks (runner : Runner) : IO Unit := do
  let fixture ← loadJson "multihash-examples.json"
  for item in (← jArr "multihash-examples.json" fixture "cases") do
    for encoding in (← jArr "multihash-examples.json" item "encodings") do
      let kind ← jStr "multihash-examples.json" encoding "kind"
      let text ← jStr "multihash-examples.json" encoding "value"
      let input ← if kind == "hex" then unhex "multihash-examples.json" text
        else
          match baseNamed? kind with
          | none => throw <| IO.userError s!"unsupported captured multihash encoding {kind}"
          | some base =>
              let prefixed := String.singleton base.prefixChar ++ text
              match Multibase.decode? prefixed with
              | .error e => throw <| IO.userError s!"captured multihash base decode: {repr e}"
              | .ok (_, bytes) =>
                  runner.check "captured multihash text re-encodes exactly"
                    (match Multibase.encode? base bytes with | .ok got => got == prefixed | .error _ => false)
                  pure bytes
      match Multihash.ofByteArray? input with
      | .error e => runner.check s!"multihash fixture decode: {repr e}" false
      | .ok value =>
          runner.check "multihash fixture byte-exact re-encode" (Multihash.toByteArray value == input)
          runner.check "multihash fixture model pin" (Bytes.checkModelPins hashProduction [input])
          runner.check "captured multihash has the named algorithm"
            (value.code.name == (← jStr "multihash-examples.json" item "algorithm"))

  let mut samples := []
  for seed in List.range 256 do
    let code := HashCode.all[seed % HashCode.all.length]?.getD .identity
    let digest := (List.range (seed % 65)).map fun j => (seed + j * 113) % 256
    samples := (← hashValue code digest) :: samples
  runner.check "multihash generic roundtrip harness" (Bytes.checkRoundTrips samples)
  runner.check "multihash byte encoder agrees with its model"
    (samples.all fun value => Multihash.toByteArray value == Bytes.ofNatList (Multihash.encode value))
  runner.check "multihash generated production/model pin"
    (Bytes.checkModelPins hashProduction (samples.map Multihash.toByteArray))

  let malformed : List (List Nat × Error) := [
    ([], .framing .truncated), ([0], .framing .truncated),
    ([0, 2, 1], .framing .truncated), ([0, 0, 0], .badDigest),
    ([0x80, 0, 0], .framing .malformed), ([0, 0x80, 0], .framing .malformed),
    (List.replicate 9 0x80, .framing .malformed),
    ([0] ++ List.replicate 9 0x80, .framing .malformed),
    (Wire.encodeNat (2 ^ 62) ++ [0], .unknownHash),
    ([0] ++ Wire.encodeNat (maxDigestBytes + 1), .overCap)]
  for (input, error) in malformed do
    runner.check "multihash detailed rejection" (hashError input error)
  runner.check "multihash model rejects a non-byte digest"
    (match Multihash.decode? [0, 1, 256] with
      | .error (.framing .malformed) => true | _ => false)
  let boundary ← hashValue .identity (List.replicate maxDigestBytes 0)
  runner.check "multihash at the digest cap" (Bytes.checkRoundTrips [boundary])
  runner.check "multihash production at the digest cap"
    (Bytes.checkModelPins hashProduction [Multihash.toByteArray boundary])
  for seed in List.range 2048 do
    let bytes := Bytes.ofNatList ((List.range (seed % 25)).map fun j =>
      (seed * 71 + j * 151 + j * j) % 256)
    runner.check "multihash hostile buffer model pin" (Bytes.checkModelPins hashProduction [bytes])

/-- The standalone CID decoder validates its consumed buffer before returning. -/
private def cidProduction (input : ByteArray) :
    Except Bytes.DecodeError (Cid × List Nat) := do
  let value ← (Cid.ofByteArray? input).mapError Error.toDecodeError
  .ok (value, [])

/-- Version invariants and nested multihash framing are exercised together. -/
private def cidChecks (runner : Runner) : IO Unit := do
  let bare := "QmYyQSo1c1Ym7orWxLYvCrM2EmxFTANf8wXmmE7DWjhx5N"
  let prefixed := "bafzbeie5745rpv2m6tjyuugywy4d5ewrqgqqhfnf445he3omzpjbx5xqxe"
  match Cid.ofString? bare, Cid.ofString? prefixed with
  | .ok v0, .ok v1 =>
      runner.check "captured CIDv0 text" (Cid.toString v0 == bare)
      runner.check "captured CIDv1 text" (Cid.toString v1 == prefixed)
      runner.check "captured CID forms retain the same hash" (v0.hash == v1.hash)
  | _, _ => runner.check "captured CID text parses" false
  let peerExamples ← loadJson "keys-peer-ids.json"
  for row in (← jArr "peer text examples" peerExamples "peerIdExamples") do
    let text ← jStr "peer text examples" row "string"
    match Multiaddr.peerBytes? text with
    | .error e => runner.check s!"captured peer text {text}: {repr e}" false
    | .ok bytes =>
        match Multihash.decode? bytes with
        | .error e => runner.check s!"captured peer multihash: {repr e}" false
        | .ok (hash, _) =>
            let cid := Cid.v1 .«p2p-key» hash
            runner.check "each captured peer hash has a lawful CIDv1 form"
              (match Cid.ofString? cid.toString with | .ok got => got == cid | .error _ => false)
            runner.check "each captured peer form retains its hash"
              ((Multiaddr.peerBytes? cid.toString).toOption == some bytes)
  let mut values := []
  for seed in List.range 128 do
    let hash ← hashValue .«sha2-256» ((List.range 32).map fun j => (seed + j * 61) % 256)
    let v0 ← match Cid.v0? hash with
      | .ok value => pure value
      | .error e => throw <| IO.userError s!"bad generated CIDv0: {repr e}"
    let codec := ContentCodec.all[seed % ContentCodec.all.length]?.getD .raw
    let v1 := Cid.v1 codec hash
    values := v0 :: v1 :: values
    for value in [v0, v1] do
      runner.check "CID generated text roundtrip"
        (match Cid.ofString? value.toString with | .ok got => got == value | .error _ => false)
  runner.check "CID generic model roundtrips" (Bytes.checkRoundTrips values)
  runner.check "CID byte encoder agrees with its model"
    (values.all fun value => Cid.toByteArray value == Bytes.ofNatList (Cid.encode value))
  runner.check "CID generated production/model pins"
    (Bytes.checkModelPins cidProduction (values.map Cid.toByteArray))
  let malformed : List (List Nat) := [[], [0], [2], [3], [1],
    [1] ++ Wire.encodeNat (2 ^ 62), [1, 0x55],
    [18, 31] ++ List.replicate 31 0,
    [18, 32] ++ List.replicate 32 0 ++ [0],
    [0x81, 0, 0x55, 0, 0]]
  for input in malformed do
    let model := match Cid.decode? input with | .error _ => true | .ok _ => false
    let bytes := Bytes.ofNatList input
    runner.check "CID malformed input is rejected" model
    runner.check "CID rejection has the same production/model result"
      (Bytes.checkModelPins cidProduction [bytes])
  for seed in List.range 1024 do
    let bytes := Bytes.ofNatList ((List.range (seed % 29)).map fun j =>
      (seed * 83 + j * 137 + j * j) % 256)
    runner.check "CID hostile buffer pin" (Bytes.checkModelPins cidProduction [bytes])

/-- The count-to-remainder adapter rejects an impossible consumed count. -/
private def componentProduction (input : ByteArray) :
    Except Bytes.DecodeError (ComponentWire.Frame × List Nat) := do
  let (frame, used) ← (ComponentWire.decodeAtB? input).mapError Error.toDecodeError
  if used ≤ input.size then .ok (frame, (Bytes.toNatList input).drop used)
  else .error .malformed

/-- The sample rule checks the total budget and terminal-path ordering. -/
private def acceptSequence (frames : List ComponentWire.Frame) : Bool :=
  (SequenceWire.encodeFrames frames).length ≤ maxAddressBytes &&
    frames.dropLast.all (fun frame => frame.proto != .unix)

/-- A standalone sequence consumes its complete buffer. -/
private def sequenceProduction (input : ByteArray) :
    Except Bytes.DecodeError (SequenceWire.Value acceptSequence × List Nat) := do
  let (value, used) ← (SequenceWire.decodeB? acceptSequence input).mapError Error.toDecodeError
  if used = input.size then .ok (value, []) else .error .malformed

/-- All registry widths run, including zero-size and variable-size components. -/
private def componentChecks (runner : Runner) : IO Unit := do
  let mut frames : List ComponentWire.Frame := []
  for protocol in Protocol.all do
    let count := protocol.fixedBytes?.getD 19
    let value := (List.range count).map fun n => (n * 97 + 13) % 256
    match ComponentWire.ofValue? protocol value with
    | .error e => runner.check s!"registry component construction: {repr e}" false
    | .ok frame =>
        frames := frame :: frames
        runner.check "component byte encoder agrees with its model"
          (ComponentWire.toByteArray frame == Bytes.ofNatList (ComponentWire.encode frame))
        let withTail := Bytes.ofNatList (ComponentWire.encode frame ++ [255, 17, 8])
        runner.check "component model pin retains its suffix"
          (Bytes.checkModelPins componentProduction [withTail])
  runner.check "all registry component widths roundtrip" (Bytes.checkRoundTrips frames)
  let allowed := frames.filter (fun frame => frame.proto != .unix)
  runner.check "sequence byte encoder agrees with its model"
    (SequenceWire.encodeFramesB allowed == Bytes.ofNatList (SequenceWire.encodeFrames allowed))
  if h : acceptSequence allowed = true then
    let sequence : SequenceWire.Value acceptSequence := ⟨allowed, h⟩
    runner.check "multi-component sequence roundtrip" (Bytes.checkRoundTrips [sequence])
    runner.check "multi-component sequence production/model pin"
      (Bytes.checkModelPins sequenceProduction [Bytes.ofNatList (SequenceWire.encode sequence)])
  else runner.check "valid component sequence setup" false
  let repeated := frames.filter (fun frame => frame.proto == .tls)
  let long := (List.replicate 2048 repeated).flatten
  if h : acceptSequence long = true then
    let value : SequenceWire.Value acceptSequence := ⟨long, h⟩
    runner.check "many valueless components preserve their order" (Bytes.checkRoundTrips [value])
    runner.check "many valueless components preserve byte offsets"
      (Bytes.checkModelPins sequenceProduction [Bytes.ofNatList (SequenceWire.encode value)])
  else runner.check "long component sequence setup" false
  match ComponentWire.ofValue? .unix [47, 120], ComponentWire.ofValue? .tls [] with
  | .ok path, .ok tls =>
      let input := Bytes.ofNatList (SequenceWire.encodeFrames [path, tls])
      runner.check "whole-sequence rule rejects a component after unix"
        (match SequenceWire.decodeB? acceptSequence input with | .error .badAddress => true | _ => false)
  | _, _ => runner.check "terminal-path sequence setup" false
  for seed in List.range 2048 do
    let input := Bytes.ofNatList ((List.range (seed % 31)).map fun n =>
      (seed * 91 + n * 113 + n * n) % 256)
    runner.check "component hostile buffer model pin" (Bytes.checkModelPins componentProduction [input])
    runner.check "sequence hostile buffer model pin" (Bytes.checkModelPins sequenceProduction [input])

/-- IP and percent text behavior is independent of remembered peer-address spelling. -/
private def addressTextChecks (runner : Runner) : IO Unit := do
  for text in ["0.0.0.0", "127.0.0.1", "192.0.2.1", "255.255.255.255"] do
    runner.check "strict IPv4 text roundtrip"
      (match Multiaddr.parseIp4? text with
        | .ok bytes => match Multiaddr.ip4String? bytes with | .ok got => got == text | _ => false
        | .error _ => false)
  for text in ["010.0.0.1", "256.0.0.1", "1_0.0.0.1", "+1.0.0.1", "1.2.3", "1.2.3.4.", " 1.2.3.4"] do
    runner.check "strict IPv4 rejects malformed octets"
      (match Multiaddr.parseIp4? text with | .error _ => true | .ok _ => false)
  for (text, expected) in [("0:0:0:0:0:0:0:0", "::"), ("::1", "::1"),
      ("2001:0db8:0:0:1:0:0:1", "2001:db8::1:0:0:1"),
      ("::ffff:192.0.2.1", "::ffff:192.0.2.1"), ("2001:db8::", "2001:db8::")] do
    runner.check "IPv6 canonical text"
      (match Multiaddr.parseIp6? text with
        | .ok bytes => match Multiaddr.ip6String? bytes with | .ok got => got == expected | _ => false
        | .error _ => false)
  for text in [":::1", "1::2::3", "1:2:3:4:5:6:7", "1:2:3:4:5:6:7:8:9",
      "00123::1", "1_0::1", "::ffff:010.0.0.1"] do
    runner.check "IPv6 rejects malformed text"
      (match Multiaddr.parseIp6? text with | .error _ => true | .ok _ => false)
  for text in ["0", "65535", "00080"] do
    runner.check "ASCII decimal port accepts valid values"
      (match Multiaddr.decimal? text 65536 with | .ok _ => true | .error _ => false)
  for text in ["", "6_5535", "65536", "+80", "80 "] do
    runner.check "ASCII decimal port rejects separators and overflow"
      (match Multiaddr.decimal? text 65536 with | .error _ => true | .ok _ => false)
  runner.check "percent encoding operates on UTF-8 bytes"
    (Multiaddr.percentEncode "é/abc?x" == "%C3%A9%2Fabc%3Fx")
  for text in ["", "plain-_.~", "é", "hello world", "/a/b", "日", "x%y", "\x00"] do
    runner.check "UTF-8 percent roundtrip"
      (match Multiaddr.percentDecode? (Multiaddr.percentEncode text) with
        | .ok got => got == text | .error _ => false)
  for text in ["%", "%0", "%GG", "%FF", "%C3"] do
    runner.check "percent decoding rejects malformed escapes and invalid UTF-8"
      (match Multiaddr.percentDecode? text with | .error _ => true | .ok _ => false)

/-- Run the package suites under the shared driver. -/
def run (runner : Runner) : IO Unit := do
  runner.section "multiformats" "pinned registries, base58 examples, multihash-examples.json"
  registryChecks runner
  base58Checks runner
  multibaseChecks runner
  hashChecks runner
  cidChecks runner
  componentChecks runner
  addressTextChecks runner

end Tests.Multiformats
