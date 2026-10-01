import Tests.Support

/-!
# Multiaddr suite (codec)

Mirrors (all pinned in VECTORS.lock, extracted by scripts/extract-vectors.py):
- multiformats/go-multiaddr `multiaddr_test.go`: TestConstructFails,
  TestConstructSucceeds, TestStringToBytes, TestBytesToString, TestRoundTrip,
  TestIPFSvP2P, TestInvalidP2PAddrBytes, TestInvalidP2PAddrString
- multiformats/js-multiaddr `test/index.spec.ts`: describe('variants'),
  describe('normalize'), invalid-address throw tests
- multiformats/multiaddr `protocols.csv`: the full protocol table

Phase 1 steps 8-10 removed the phase-0 crutches: every protocol in
protocols.csv is implemented, so there is no `supported` filter and no gap
annotations. Vectors marked `knownDivergence` exercise behaviour where the
upstream Go and JS suites disagree (the `memory` value type); we follow
Go/Rust and skip those with a printed reason.
-/

open LeanP2P Tests

namespace Tests.Multiaddr

/-- JS roundTrip expectation: /ipfs/ prints as /p2p/. -/
def canon (s : String) : String := s.replace "/ipfs/" "/p2p/"

/-- protocol.csv name -> a representative component (for code checks).
`ipfs` is an alias of `p2p`. -/
def protoComponent : String → Option AddrComponent
  | "ip4" => some (.ip4 0 0 0 0)
  | "tcp" => some (.tcp 0)
  | "udp" => some (.udp 0)
  | "dccp" => some (.dccp 0)
  | "sctp" => some (.sctp 0)
  | "udt" => some .udt
  | "utp" => some .utp
  | "noise" => some .noise
  | "ip6" => some (.ip6 [])
  | "ip6zone" => some (.ip6zone "")
  | "ipcidr" => some (.ipcidr 0)
  | "dns" => some (.dns "")
  | "dns4" => some (.dns4 "")
  | "dns6" => some (.dns6 "")
  | "dnsaddr" => some (.dnsaddr "")
  | "sni" => some (.sni "")
  | "unix" => some (.unix "/")
  | "p2p" => some (.p2p [] false)
  | "ipfs" => some (.p2p [] false)
  | "onion" => some (.onion [] 0)
  | "onion3" => some (.onion3 [] 0)
  | "garlic64" => some (.garlic64 [])
  | "garlic32" => some (.garlic32 [])
  | "tls" => some .tls
  | "quic" => some .quic
  | "quic-v1" => some .quicV1
  | "webtransport" => some .webtransport
  | "certhash" => some (.certhash [])
  | "http" => some .http
  | "http-path" => some (.httpPath "")
  | "https" => some .https
  | "ws" => some .ws
  | "wss" => some .wss
  | "p2p-websocket-star" => some .p2pWebsocketStar
  | "p2p-stardust" => some .p2pStardust
  | "p2p-webrtc-star" => some .p2pWebrtcStar
  | "p2p-webrtc-direct" => some .p2pWebrtcDirect
  | "webrtc-direct" => some .webrtcDirect
  | "webrtc" => some .webrtc
  | "p2p-circuit" => some .p2pCircuit
  | "memory" => some (.memory 0)
  | "ech" => some (.ech "")
  | _ => none

def run (r : Runner) : IO Unit := do
  r.section "multiaddr"
    "multiformats/go-multiaddr multiaddr_test.go; multiformats/js-multiaddr \
     test/index.spec.ts; multiformats/multiaddr protocols.csv"

  -- ### TestConstructSucceeds (parse must accept)
  let j ← loadJson "multiaddr-go-construct-succeeds.json"
  for c in (← jArr "multiaddr-go-construct-succeeds.json" j "cases") do
    let s ← jStr "multiaddr-go-construct-succeeds.json" c "string"
    r.check s!"go construct {s}" ((Multiaddr.parse? s).isSome)

  -- ### TestConstructFails (parse must reject)
  let j ← loadJson "multiaddr-go-construct-fails.json"
  for c in (← jArr "multiaddr-go-construct-fails.json" j "cases") do
    let s ← jStr "multiaddr-go-construct-fails.json" c "string"
    r.check s!"go construct-reject \"{s}\"" (Multiaddr.parse? s == none)

  -- ### TestStringToBytes / TestBytesToString
  for (file, kind) in
      [("multiaddr-go-string-to-bytes.json", "text->bytes"),
       ("multiaddr-go-bytes-to-string.json", "bytes->text")] do
    let j ← loadJson file
    for c in (← jArr file j "cases") do
      let s ← jStr file c "string"
      let h ← jStr file c "bytesHex"
      let wantBytes ← hexBytes h
      match kind with
      | "text->bytes" =>
        r.check s!"go {kind} {s}"
          ((Multiaddr.parse? s).map Multiaddr.toBytes == some wantBytes)
      | _ =>
        r.check s!"go {kind} {s}"
          ((Multiaddr.ofBytes? wantBytes).map Multiaddr.toString == some s)

  -- ### TestRoundTrip (text form must round-trip byte-exactly)
  let j ← loadJson "multiaddr-go-round-trip.json"
  for c in (← jArr "multiaddr-go-round-trip.json" j "cases") do
    let s ← jStr "multiaddr-go-round-trip.json" c "string"
    r.check s!"go roundtrip {s}"
      ((Multiaddr.parse? s).map Multiaddr.toString == some s)

  -- ### TestIPFSvP2P (both spellings, /p2p/ canonical)
  let j ← loadJson "multiaddr-go-ipfs-v-p2p.json"
  let p2p ← jStr "multiaddr-go-ipfs-v-p2p.json" j "p2p"
  let ipfs ← jStr "multiaddr-go-ipfs-v-p2p.json" j "ipfs"
  r.check "go ipfs-v-p2p p2p form" ((Multiaddr.parse? p2p).map Multiaddr.toString == some p2p)
  r.check "go ipfs-v-p2p ipfs alias" ((Multiaddr.parse? ipfs).map Multiaddr.toString == some p2p)

  -- ### TestInvalidP2PAddrBytes / TestInvalidP2PAddrString
  let j ← loadJson "multiaddr-go-invalid-p2p.json"
  let badHex ← jStr "multiaddr-go-invalid-p2p.json" j "bytesHex"
  let badBytes ← hexBytes badHex
  r.check "go invalid-p2p bytes" (Multiaddr.ofBytes? badBytes == none)
  for c in (← jArr "multiaddr-go-invalid-p2p.json" j "strings") do
    let s ← jStr "multiaddr-go-invalid-p2p.json" c "string"
    r.check s!"go invalid-p2p {s}" (Multiaddr.parse? s == none)

  -- ### js variants (round trip, /ipfs/ -> /p2p/)
  let j ← loadJson "multiaddr-js-variants.json"
  for c in (← jArr "multiaddr-js-variants.json" j "cases") do
    let name ← jStr "multiaddr-js-variants.json" c "name"
    let s ← jStr "multiaddr-js-variants.json" c "value"
    match ← knownDivergence? "multiaddr-js-variants.json" c with
    | some why =>
      r.skip s!"js variants {name}" why
    | none =>
      r.check s!"js variants {name}"
        ((Multiaddr.parse? s).map Multiaddr.toString == some (canon s))

  -- ### js normalize
  let j ← loadJson "multiaddr-js-normalize.json"
  for c in (← jArr "multiaddr-js-normalize.json" j "cases") do
    let name ← jStr "multiaddr-js-normalize.json" c "name"
    let input ← jStr "multiaddr-js-normalize.json" c "input"
    let output ← jStr "multiaddr-js-normalize.json" c "output"
    r.check s!"js normalize {name}"
      ((Multiaddr.parse? input).map Multiaddr.toString == some output)

  -- ### js invalid / unknown protocols
  let j ← loadJson "multiaddr-js-invalid.json"
  for c in (← jArr "multiaddr-js-invalid.json" j "cases") do
    let s ← jStr "multiaddr-js-invalid.json" c "string"
    r.check s!"js invalid {s}" (Multiaddr.parse? s == none)

  -- ### protocols.csv: the FULL table must be implemented with exact codes
  let j ← loadJson "multiaddr-protocols.json"
  let csv : List (String × Nat) ← (← jArr "multiaddr-protocols.json" j "protocols").mapM
    fun p => do pure (← jStr "multiaddr-protocols.json" p "name",
                      ← jNat "multiaddr-protocols.json" p "code")
  for (name, csvCode) in csv do
    match protoComponent name with
    | some comp =>
        r.check s!"protocols.csv code {name}" (Multiaddr.code comp == csvCode)
        -- `ipfs` is an alias: the component prints as `p2p`
        unless name == "ipfs" do
          r.check s!"protocols.csv name {name}" (Multiaddr.name comp == name)
    | none => r.check s!"protocols.csv implements {name}" false
  r.check "protocols.csv row count" (csv.length == 42)

end Tests.Multiaddr
