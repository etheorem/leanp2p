import Tests.Support

/-!
# Multiaddr operations + decoder-totality suite

Mirrors (pinned in VECTORS.lock, extracted by scripts/extract-vectors.py):
- go-multiaddr: TestGetValue, TestEncapsulate, TestDecapsulate, TestEqual,
  TestBytesSplitAndJoin, TestFilterAddrs, TestContains, TestUniqueAddrs,
  TestZone, TestDNS, TestHTTPPath, the *Marshaler tests
- js-multiaddr: .getComponents, .decapsulate, .decapsulateCode, .equals,
  construction

Phase 1 step 10 adds decoder-totality property tests: pseudo-random byte
strings (deterministic LCG, mirroring Go's FuzzNewMultiaddrBytes) and
randomly generated component sequences must round-trip. Lean functions are
total, so "never panics" holds by construction; the checkable property is
that accepted inputs round-trip.
-/

open LeanP2P Tests

namespace Tests.MultiaddrOps

/-- Components normalized to the binary form: the p2p print-form flag is
not carried on the wire, so binary round trips compare modulo the flag
(Go's components carry no such flag either). -/
def norm : AddrComponent → AddrComponent
  | .p2p mh _ => .p2p mh false
  | c => c

/-- Deterministic LCG (glibc-style constants) for reproducible fuzzing. -/
def lcg (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

/-- Random byte string of length `n`. -/
def randBytes (seed : Nat) (n : Nat) : List Nat × Nat :=
  let rec go (s : Nat) (k : Nat) (acc : List Nat) : List Nat × Nat :=
    match k with
    | 0 => (acc.reverse, s)
    | k + 1 =>
        let s := lcg s
        go s k ((s / 65536) % 256 :: acc)
  go seed n []

/-- A structured component generator over many kinds. Every generated
component satisfies the decoder's validation rules, so the binary codec
must accept it. `unix` is excluded here: it is terminal (no component may
follow), and the fuzz loops append it separately as the last component. -/
def randComponent (s : Nat) : AddrComponent × Nat :=
  let s1 := lcg s
  let name : Nat → String := fun seed =>
    String.ofList ((List.range (seed % 8 + 1)).map
      (fun i => Char.ofNat ('a'.toNat + (seed + i) % 26)))
  match s1 % 18 with
  | 0 => (.tcp (s1 % 65536), s1)
  | 1 => (.udp (lcg s1 % 65536), lcg s1)
  | 2 => (.dccp (lcg s1 % 65536), lcg s1)
  | 3 => (.sctp (lcg s1 % 65536), lcg s1)
  | 4 => (.ip4 (lcg s1 % 256) (lcg s1 % 256) (lcg s1 % 256) (lcg s1 % 256), lcg s1)
  | 5 => (.ip6 ((List.range 8).map (fun _ => lcg s1 % 65536)), lcg s1)
  | 6 => (.ip6zone (name s1), lcg s1)  -- must be followed by ip6: see genAppend
  | 7 => (.ipcidr (lcg s1 % 256), lcg s1)
  | 8 => (.dns (name s1), lcg s1)
  | 9 => (.dns4 (name s1), lcg s1)
  | 10 => (.dns6 (name s1), lcg s1)
  | 11 => (.dnsaddr (name s1), lcg s1)
  | 12 => (.sni (name s1), lcg s1)
  | 13 => (.quic, lcg s1)
  | 14 => (.utp, lcg s1)
  | 15 => (.webtransport, lcg s1)
  | 16 => (.p2p ([0x12, 0x20] ++ List.replicate 32 (s1 % 256)) false, lcg s1)
  | _ => (.memory (lcg s1 % 18446744073709551615 + 1), lcg s1)

/-- Append `c` respecting the decoder's adjacency rules: `ip6zone` must be
followed by `ip6`. Returns the (possibly extended) list and the seed. -/
def genAppend (cs : List AddrComponent) (c : AddrComponent) (s : Nat) :
    List AddrComponent × Nat :=
  match cs.getLast? with
  | some (.ip6zone _) =>
      ((cs ++ [.ip6 ((List.range 8).map (fun _ => lcg s % 65536))]) ++ [c], lcg s)
  | _ => (cs ++ [c], s)

/-- Protocol name -> code for the TestGetValue vectors. -/
def gvCode : String → Nat
  | "ip4" => 4 | "tcp" => 6 | "udp" => 273 | "utp" => 302 | "tls" => 448
  | "ipfs" => 421 | "p2p" => 421 | "unix" => 400 | "http-path" => 481
  | "ip6" => 41 | "memory" => 777 | _ => 0

def run (r : Runner) : IO Unit := do
  r.section "multiaddr ops + totality"
    "go-multiaddr TestGetValue/Encapsulate/Decapsulate/Equal/SplitAndJoin/\
     FilterAddrs/Contains/UniqueAddrs/Zone/DNS/HTTPPath/*Marshaler; \
     js-multiaddr .getComponents/.decapsulate/.decapsulateCode/.equals; \
     FuzzNewMultiaddrBytes/FuzzSplitRoundtrip (as property tests)"

  -- ### TestGetValue
  let j ← loadJson "multiaddr-go-get-value.json"
  for c in (← jArr "multiaddr-go-get-value.json" j "cases") do
    let addr ← jStr "multiaddr-go-get-value.json" c "addr"
    match Multiaddr.parse? addr with
    | none => r.check s!"go get-value parse {addr}" false
    | some m =>
      for chk in (← jArr "multiaddr-go-get-value.json" c "checks") do
        let proto ← jStr "multiaddr-go-get-value.json" chk "proto"
        let want ← jStr "multiaddr-go-get-value.json" chk "value"
        r.check s!"go get-value {addr} {proto}"
          (Multiaddr.valueForProtocol? m (gvCode proto) == some want)
      for proto in (← jStrs "multiaddr-go-get-value.json" c "missing") do
        r.check s!"go get-value missing {addr} {proto}"
          (Multiaddr.valueForProtocol? m (gvCode proto) == none)

  -- ### TestEncapsulate
  let j ← loadJson "multiaddr-go-encapsulate.json"
  for c in (← jArr "multiaddr-go-encapsulate.json" j "encapsulate") do
    let left ← jStr "multiaddr-go-encapsulate.json" c "left"
    let right ← jStr "multiaddr-go-encapsulate.json" c "right"
    let expected ← jStr "multiaddr-go-encapsulate.json" c "expected"
    let name := s!"go encapsulate {left} + {right}"
    match Multiaddr.parse? left, Multiaddr.parse? right with
    | some l, some rr =>
        r.check name (Multiaddr.toString (l.encapsulate rr) == expected)
        r.check s!"{name} decapsulate"
          ((Multiaddr.decapsulate? (l.encapsulate rr) rr).map Multiaddr.toString
            == some left)
    | _, _ => r.check name false

  -- ### TestEncapsulate's decapsulate half (null expected = nil)
  for c in (← jArr "multiaddr-go-encapsulate.json" j "decapsulate") do
    let left ← jStr "multiaddr-go-encapsulate.json" c "left"
    let right ← jStr "multiaddr-go-encapsulate.json" c "right"
    let expected ← jStr? "multiaddr-go-encapsulate.json" c "expected"
    let name := s!"go encapsulate decapsulate {left} - {right}"
    match Multiaddr.parse? left, Multiaddr.parse? right with
    | some l, some rr =>
        r.check name
          ((Multiaddr.decapsulate? l rr).map Multiaddr.toString == expected)
    | _, _ => r.check name false

  -- ### TestDecapsulate (expected "" means nil / nothing left)
  let j ← loadJson "multiaddr-go-decapsulate.json"
  for c in (← jArr "multiaddr-go-decapsulate.json" j "cases") do
    let left ← jStr "multiaddr-go-decapsulate.json" c "left"
    let right ← jStr "multiaddr-go-decapsulate.json" c "right"
    let expected ← jStr "multiaddr-go-decapsulate.json" c "expected"
    let name := s!"go decapsulate {left} - {right}"
    match Multiaddr.parse? left, Multiaddr.parse? right with
    | some l, some rr =>
        let got := (Multiaddr.decapsulate? l rr).map Multiaddr.toString
        r.check name (got == (if expected == "" then none else some expected))
    | _, _ => r.check name false

  -- ### TestEqual
  let j ← loadJson "multiaddr-go-equal.json"
  for c in (← jArr "multiaddr-go-equal.json" j "pairs") do
    let a ← jStr "multiaddr-go-equal.json" c "a"
    let b ← jStr "multiaddr-go-equal.json" c "b"
    let want ← jBool "multiaddr-go-equal.json" c "equal"
    let got := match Multiaddr.parse? a, Multiaddr.parse? b with
      | some ma, some mb => Multiaddr.equal ma mb
      | _, _ => false
    r.check s!"go equal {a} vs {b}" (got == want)

  -- ### TestProtocols / TestProtocolsWithString
  let j ← loadJson "multiaddr-go-protocols-with-string.json"
  let goodPairs : List (String × List String) ←
    (← jArr "multiaddr-go-protocols-with-string.json" j "good").mapM fun c => do
      pure ((← jStr "multiaddr-go-protocols-with-string.json" c "addr"),
             (← jStrs "multiaddr-go-protocols-with-string.json" c "protocols"))
  for (addr, protos) in goodPairs do
    let got := (Multiaddr.protocolsWithString? addr).map (fun ps => ps.map (fun p => p.2))
    r.check s!"go protocols-with-string {addr}" (got == some protos)
  for addr in (← jStrs "multiaddr-go-protocols-with-string.json" j "bad") do
    r.check s!"go protocols-with-string reject {addr}" (Multiaddr.parse? addr == none)

  -- ### TestBytesSplitAndJoin
  let j ← loadJson "multiaddr-go-split.json"
  for c in (← jArr "multiaddr-go-split.json" j "cases") do
    let addr ← jStr "multiaddr-go-split.json" c "addr"
    let parts ← jStrs "multiaddr-go-split.json" c "parts"
    match Multiaddr.parse? addr with
    | none => r.check s!"go split parse {addr}" false
    | some m =>
      let split := Multiaddr.split m
      r.check s!"go split {addr} count" (split.length == parts.length)
      for (sm, want) in split.zip parts do
        r.check s!"go split part {want}" (Multiaddr.toString sm == want)
      r.check s!"go join {addr}" (Multiaddr.equal (Multiaddr.join split) m)

  -- ### TestFilterAddrs (filter: first protocol code is ip4)
  let j ← loadJson "multiaddr-go-filter-addrs.json"
  let good ← jStrs "multiaddr-go-filter-addrs.json" j "good"
  let bad ← jStrs "multiaddr-go-filter-addrs.json" j "bad"
  let ip4First (m : Multiaddr) : Bool :=
    (m.components.head?).map Multiaddr.code == some 4
  let parsedGood := good.filterMap Multiaddr.parse?
  let parsedBad := bad.filterMap Multiaddr.parse?
  r.check "go filter-addrs all parsed" ((parsedGood.length + parsedBad.length) == good.length + bad.length)
  r.check "go filter-addrs good kept"
    ((Multiaddr.filterAddrs parsedGood ip4First).map Multiaddr.toString == good)
  r.check "go filter-addrs bad dropped"
    (Multiaddr.filterAddrs parsedBad ip4First == [])

  -- ### TestContains
  let j ← loadJson "multiaddr-go-contains.json"
  let addrs ← jStrs "multiaddr-go-contains.json" j "addrs"
  let parsed := addrs.filterMap Multiaddr.parse?
  for a in addrs do
    match Multiaddr.parse? a with
    | some m => r.check s!"go contains member {a}" (Multiaddr.contains parsed m)
    | none => r.check s!"go contains parse {a}" false
  for a in (← jStrs "multiaddr-go-contains.json" j "nonMembers") do
    match Multiaddr.parse? a with
    | some m => r.check s!"go contains non-member {a}" (!Multiaddr.contains parsed m)
    | none => r.check s!"go contains parse {a}" false

  -- ### TestUniqueAddrs (Go requires: every `out` element is kept)
  let j ← loadJson "multiaddr-go-unique-addrs.json"
  for (tbl, i) in (← jArr "multiaddr-go-unique-addrs.json" j "tables").zipIdx do
    let ins ← jStrs "multiaddr-go-unique-addrs.json" tbl "in"
    let outs ← jStrs "multiaddr-go-unique-addrs.json" tbl "out"
    let parsedIn := ins.filterMap Multiaddr.parse?
    let deduped := (Multiaddr.uniqueAddrs parsedIn).map Multiaddr.toString
    r.check s!"go unique-addrs {i} idempotent"
      ((Multiaddr.uniqueAddrs (deduped.filterMap Multiaddr.parse?)).map Multiaddr.toString
        == deduped)
    for o in outs do
      r.check s!"go unique-addrs {i} keeps {o}" (deduped.contains o)

  -- ### TestZone
  let j ← loadJson "multiaddr-go-zone.json"
  let zs ← jStr "multiaddr-go-zone.json" j "string"
  let zHex ← jStr "multiaddr-go-zone.json" j "bytesHex"
  let zBytes ← hexBytes zHex
  r.check "go zone text->bytes"
    ((Multiaddr.parse? zs).map Multiaddr.toBytes == some zBytes)
  r.check "go zone bytes->text"
    ((Multiaddr.ofBytes? zBytes).map Multiaddr.toString == some zs)

  -- ### TestDNS (bytes -> string -> bytes round trip)
  let j ← loadJson "multiaddr-go-dns.json"
  let dHex ← jStr "multiaddr-go-dns.json" j "bytesHex"
  let dBytes ← hexBytes dHex
  match Multiaddr.ofBytes? dBytes with
  | some m =>
      let s := Multiaddr.toString m
      r.check "go dns string->bytes round trip"
        ((Multiaddr.parse? s).map Multiaddr.toBytes == some dBytes)
  | none => r.check "go dns bytes parse" false

  -- ### TestHTTPPath
  let j ← loadJson "multiaddr-go-http-path.json"
  let bad ← jStr "multiaddr-go-http-path.json" j "bad"
  r.check "go http-path rejects bad escape" (Multiaddr.parse? bad == none)
  for s in (← jStrs "multiaddr-go-http-path.json" j "roundTrip") do
    r.check s!"go http-path roundtrip {s}"
      ((Multiaddr.parse? s).map Multiaddr.toString == some s)
  let vc ← jObj "multiaddr-go-http-path.json" j "valueCase"
  let vcAddr ← jStr "multiaddr-go-http-path.json" vc "addr"
  let vcValue ← jStr "multiaddr-go-http-path.json" vc "value"
  match Multiaddr.parse? vcAddr with
  | some m =>
      r.check s!"go http-path value {vcAddr}"
        (Multiaddr.valueForProtocol? m 481 == some vcValue)
  | none => r.check s!"go http-path parse {vcAddr}" false

  -- ### Marshalers (binary / text / JSON round trips)
  let j ← loadJson "multiaddr-go-marshaler.json"
  let addr ← jStr "multiaddr-go-marshaler.json" j "addr"
  match Multiaddr.parse? addr with
  | some m =>
      r.check "go marshaler binary"
        (Multiaddr.ofByteArray? m.toByteArray == some m)
      r.check "go marshaler text"
        (Multiaddr.parse? (Multiaddr.toString m) == some m)
      r.check "go marshaler json"
        (Multiaddr.ofJSON? (Multiaddr.toJSON m) == some m)
  | none => r.check "go marshaler parse" false

  -- ### js .getComponents
  let j ← loadJson "multiaddr-js-get-components.json"
  for c in (← jArr "multiaddr-js-get-components.json" j "cases") do
    let addr ← jStr "multiaddr-js-get-components.json" c "addr"
    let want ← jArr "multiaddr-js-get-components.json" c "components"
    let name := s!"js getComponents {addr}"
    match ← knownDivergence? "multiaddr-js-get-components.json" c with
    | some why => r.skip name why
    | none =>
    match Multiaddr.parse? addr with
    | some m =>
        let want' : List (Nat × String × Option String) ← want.mapM fun w => do
          pure ((← jNat "multiaddr-js-get-components.json" w "code"),
                 (← jStr "multiaddr-js-get-components.json" w "name"),
                 (← jStr? "multiaddr-js-get-components.json" w "value"))
        let got' := Multiaddr.getComponents m |>.map (fun x => (x.code, x.name, x.value))
        r.check name (got' == want')
    | none => r.check name false

  -- ### js .decapsulate (throws when not contained)
  let j ← loadJson "multiaddr-js-decapsulate.json"
  for c in (← jArr "multiaddr-js-decapsulate.json" j "cases") do
    let addr ← jStr "multiaddr-js-decapsulate.json" c "addr"
    let sub ← jStr "multiaddr-js-decapsulate.json" c "sub"
    match Multiaddr.parse? addr, Multiaddr.parse? sub with
    | some a, some s =>
        r.check s!"js decapsulate {addr} - {sub}"
          (Multiaddr.decapsulateThrow? a s == none)
    | _, _ => r.check s!"js decapsulate parse {addr}" false

  -- ### js .decapsulateCode
  let j ← loadJson "multiaddr-js-decapsulate-code.json"
  let relayTcpS ← jStr "multiaddr-js-decapsulate-code.json" j "relayTcp"
  let suffix ← jStr "multiaddr-js-decapsulate-code.json" j "relaySuffix"
  let targetS ← jStr "multiaddr-js-decapsulate-code.json" j "target"
  let code ← jNat "multiaddr-js-decapsulate-code.json" j "code"
  match Multiaddr.parse? relayTcpS, Multiaddr.parse? suffix, Multiaddr.parse? targetS with
  | some relayTcp, some suffixM, some target =>
      let relay := relayTcp.encapsulate suffixM
      let original := relay.encapsulate target
      r.check "js decapsulateCode original"
        (Multiaddr.equal (Multiaddr.decapsulateCode original code) relay)
      r.check "js decapsulateCode relay"
        (Multiaddr.equal (Multiaddr.decapsulateCode relay code) relayTcp)
      r.check "js decapsulateCode missing code unchanged"
        (Multiaddr.equal (Multiaddr.decapsulateCode relayTcp code) relayTcp)
  | _, _, _ => r.check "js decapsulateCode parse" false

  -- ### js .equals
  let j ← loadJson "multiaddr-js-equals.json"
  for c in (← jArr "multiaddr-js-equals.json" j "pairs") do
    let a ← jStr "multiaddr-js-equals.json" c "a"
    let b ← jStr "multiaddr-js-equals.json" c "b"
    let want ← jBool "multiaddr-js-equals.json" c "equal"
    r.check s!"js equals {a} vs {b}"
      ((Multiaddr.equal <$> Multiaddr.parse? a <*> Multiaddr.parse? b) == some want)

  -- ### js construction (reconstruct from string and bytes)
  let j ← loadJson "multiaddr-js-construction.json"
  let addr ← jStr "multiaddr-js-construction.json" j "addr"
  match Multiaddr.parse? addr with
  | some m =>
      r.check "js construction reconstruct string"
        (Multiaddr.parse? (Multiaddr.toString m) == some m)
      r.check "js construction reconstruct bytes"
        ((Multiaddr.ofByteArray? m.toByteArray).map Multiaddr.toString
          == some (Multiaddr.toString m))
  | none => r.check "js construction parse" false
  -- documented divergence: js parses '' into an empty address, Go rejects
  r.check "divergence empty parse rejects (Go)" (Multiaddr.parse? "" == none)
  r.check "divergence empty prints as / (js)"
    (Multiaddr.toString { components := [] } == "/")

  -- ### Regression checks (review round 2)
  -- the Go fuzz seed that exposed non-terminal unix decoding: a component
  -- after a path protocol must be rejected (9003032f3030213030)
  let seedUnix ← hexBytes "9003032f3030213030"
  r.check "regression unix is terminal in binary"
    (Multiaddr.ofBytes? seedUnix == none)
  r.check "regression unix terminal agrees with spec"
    (Multiaddr.decodeBinB (Bytes.ofNatList seedUnix)
      == Multiaddr.decodeBin seedUnix)
  -- production vs specification decoders on the go byte-vectors
  let j2 ← loadJson "multiaddr-go-string-to-bytes.json"
  for c in (← jArr "multiaddr-go-string-to-bytes.json" j2 "cases") do
    let h ← jStr "multiaddr-go-string-to-bytes.json" c "bytesHex"
    let bs ← hexBytes h
    r.check s!"equiv spec/prod {h}"
      (Multiaddr.decodeBinB (Bytes.ofNatList bs) == Multiaddr.decodeBin bs)
  -- the fmt.Sprintf construct-fail: memory above the u64 range
  r.check "regression memory above u64 rejected"
    (Multiaddr.parse? "/memory/92233720368547758081" == none)
  r.check "regression memory u64 max accepted"
    ((Multiaddr.parse? "/memory/18446744073709551615").map Multiaddr.toString
      == some "/memory/18446744073709551615")

  -- ### Decoder totality (FuzzNewMultiaddrBytes / FuzzSplitRoundtrip)
  -- Deterministic pseudo-random byte strings: every accepted input must
  -- round-trip through bytes (modulo the p2p print-form flag) and through
  -- its printed text. Lean functions are total, so no input can panic.
  let mut seed := 42
  let mut accepted := 0
  for i in [0:1500] do
    seed := lcg seed + i
    let (bs, s2) := randBytes seed ((seed / 65536) % 24 + 1)
    seed := s2
    match Multiaddr.ofByteArray? (Bytes.ofNatList bs) with
    | some m =>
        accepted := accepted + 1
        let reb := Multiaddr.ofByteArray? m.toByteArray
        r.check s!"fuzz bytes roundtrip #{i}"
          (reb.map (fun m2 => m2.components.map norm) == some (m.components.map norm))
        r.check s!"fuzz text roundtrip #{i}"
          (Multiaddr.parse? (Multiaddr.toString m) == some m)
    | none => pure ()
  r.check "fuzz accepted some inputs" (accepted > 0)

  -- Same sweep over VALID prefixes followed by perturbed tails: the tail is
  -- the encoding of extra random components, either complete (must decode
  -- and round-trip) or truncated mid-component (must fail cleanly). This
  -- reaches the decoder's inner branches far more often than pure random
  -- bytes, where almost every input dies on the first varint.
  seed := 4242
  let mut accepted2 := 0
  for i in [0:600] do
    let mut comps : List AddrComponent := []
    let mut n := lcg seed % 3 + 1
    let mut s := seed
    while n > 0 do
      let (c, s2) := randComponent s
      let (cs2, s3) := genAppend comps c s
      comps := cs2
      s := s3
      n := n - 1
    if comps.getLast? matches some (.ip6zone _) then
      comps := comps ++ [.ip6 ((List.range 8).map (fun _ => lcg s % 65536))]
    seed := lcg s
    -- build the tail: extra components, maybe truncated
    let mut extra : List AddrComponent := []
    let mut k := lcg seed % 2 + 1
    let mut s2 := seed
    while k > 0 do
      let (c, s3) := randComponent s2
      let (cs2, s4) := genAppend extra c s2
      extra := cs2
      s2 := s4
      k := k - 1
    if extra.getLast? matches some (.ip6zone _) then
      extra := extra ++ [.ip6 ((List.range 8).map (fun _ => lcg s2 % 65536))]
    let mut tail := Multiaddr.toByteArray { components := extra }
    if (lcg s2 + i) % 2 == 0 then
      tail := Bytes.ofNatList ((Bytes.toNatList tail).drop (lcg s2 % 3 + 1))
    seed := s2 + i
    let b := (Multiaddr.toByteArray { components := comps }).append tail
    match Multiaddr.ofByteArray? b with
    | some m =>
        accepted2 := accepted2 + 1
        r.check s!"fuzz prefix+tail roundtrip #{i}"
          ((Multiaddr.ofByteArray? m.toByteArray).map (fun m2 => m2.components.map norm)
            == some (m.components.map norm))
    | none => pure ()
  r.check "fuzz prefix+tail accepted many inputs" (accepted2 > 150)

  -- Structured fuzz: random component sequences round-trip through the
  -- binary codec exactly (FuzzSplitRoundtrip). An optional terminal unix
  -- path is appended last (path protocols end the address).
  seed := 7
  for i in [0:400] do
    let mut comps : List AddrComponent := []
    let mut n := lcg seed % 5 + 1
    let mut s := seed
    while n > 0 do
      let (c, s2) := randComponent s
      let (cs2, s3) := genAppend comps c s
      comps := cs2
      s := s3
      n := n - 1
    -- fix up a trailing ip6zone: it must be followed by ip6
    if comps.getLast? matches some (.ip6zone _) then
      comps := comps ++ [.ip6 ((List.range 8).map (fun _ => lcg s % 65536))]
    if s % 3 == 0 then
      let (cs2, s3) := genAppend comps
        (.unix ("/" ++ String.ofList ((List.range (s % 5 + 2)).map
          (fun k => Char.ofNat ('a'.toNat + (s + k) % 26))))) s
      comps := cs2
      s := s3
    seed := s + i
    let bs := Multiaddr.encodeBin comps
    r.check s!"fuzz structured roundtrip #{i}"
      (Multiaddr.decodeBin bs == some comps)

  -- Production vs specification equivalence (anti-drift for the ByteArray
  -- wire codec): the ByteArray decoder agrees with the List Nat proof view
  -- on every random input, and the encoders produce identical bytes.
  seed := 99
  for i in [0:600] do
    seed := lcg seed + i
    let (bs, s2) := randBytes seed ((seed / 65536) % 40 + 1)
    seed := s2
    let b := Bytes.ofNatList bs
    r.check s!"equiv decode #{i}"
      (Multiaddr.decodeBinB b == Multiaddr.decodeBin bs)
    let mut comps : List AddrComponent := []
    let mut n := lcg seed % 4 + 1
    let mut s := seed
    while n > 0 do
      let (c, s2) := randComponent s
      let (cs2, s3) := genAppend comps c s
      comps := cs2
      s := s3
      n := n - 1
    seed := s
    r.check s!"equiv encode #{i}"
      (Multiaddr.encodeBinB comps == Bytes.ofNatList (Multiaddr.encodeBin comps))

  -- ### Go fuzz seed corpora (testdata/fuzz, ported by extract-vectors.py)
  let j ← loadJson "multiaddr-go-fuzz-bytes.json"
  for (h, k) in (← jStrs "multiaddr-go-fuzz-bytes.json" j "seedsHex").zipIdx do
    match Bytes.ofHex? h with
    | none => r.check s!"go fuzz bytes {k} bad hex" false
    | some b =>
        match Multiaddr.ofByteArray? b with
        | some m =>
            r.check s!"go fuzz bytes {k} roundtrip bytes"
              ((Multiaddr.ofByteArray? m.toByteArray).map (fun m2 => m2.components.map norm)
                == some (m.components.map norm))
            r.check s!"go fuzz bytes {k} roundtrip text"
              (Multiaddr.parse? (Multiaddr.toString m) == some m)
        | none => pure ()  -- rejected seeds must only fail cleanly
  let j ← loadJson "multiaddr-go-fuzz-strings.json"
  for (s, k) in (← jStrs "multiaddr-go-fuzz-strings.json" j "seeds").zipIdx do
    match Multiaddr.parse? s with
    | some m =>
        r.check s!"go fuzz strings {k} roundtrip text"
          (Multiaddr.parse? (Multiaddr.toString m) == some m)
        r.check s!"go fuzz strings {k} roundtrip bytes"
          ((Multiaddr.ofByteArray? m.toByteArray).map (fun m2 => m2.components.map norm)
            == some (m.components.map norm))
    | none => pure ()

end Tests.MultiaddrOps
