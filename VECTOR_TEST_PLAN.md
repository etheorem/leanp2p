# Plan: from spike to passing the libp2p / multiformats vector tests

Status of the spike on 2026-09-22: `lake build` is clean and the 80 embedded
tests pass. This document lists what is missing to pass the *upstream* vector
and conformance suites, and gives an ordered plan. It does not implement
anything.

Status update 2026-09-24: **phases 0-3 are implemented** (steps 1-21).
`lake test` runs 3049 checks from extracted upstream vectors and captured
go-libp2p transcripts with 0 failures and 0 todo (4 skipped: two js-only
`memory` vectors, two documented re-sign divergences). Phases 0-2 covered
the wire codec, multiformats, the crypto backend, protobuf, keys and peer
ids. Phase 3 delivered: complete multistream-select (buffered reader,
1024-byte cap, `ls` reply framing, lazy dialer, byte-split two-party
tests, captured go-multistream traces); Noise XX (`Noise_XX_25519_ChaChaPoly_SHA256`
with ChaCha20-Poly1305 via OpenSSL, verified against Noise framework
vectors from flynn/noise and a captured go-libp2p Transport transcript);
the TLS certificate extension (all four tls.md vectors, X.509 via the
OpenSSL backend, SignedKey ASN.1 decode in Lean); yamux (12-byte header
codec with round-trip theorem, stream state machine, window accounting,
ping echo, GoAway); mplex (header varint codec with theorem, seven flags,
1 MiB cap); Ping (`/ipfs/ping/1.0.0`, 32-byte echo); Identify
(`/ipfs/id/1.0.0`, protobuf, peer-id derivation); and signed envelopes +
peer records (RFC 0002/0003) verified against captured go-libp2p
`record.Seal` output with `scripts/envelope-verify.go` for the
reverse direction. Real go-libp2p wire captures (Noise transcript,
Identify protobuf, multistream traces, envelope) live in `Tests/vectors/`.

Status update 2026-09-25: **phase 4 (real node) is implemented** (steps
22-24). Step 22 replaced every polling queue and racy `IO.Ref`
read-modify-write with promise-blocking primitives (`LeanP2P/Conc.lean`:
`Chan` over `Std.CloseableChannel`, `TaskSet` for owned/joined tasks,
mutex-guarded cells); the full suite passes under `+RTS -N1` in ~24 s and
a stress test drives 1000 ping streams (950 sequential + 50 concurrent)
through one mux session. Step 23 added a real TCP transport
(`LeanP2P/Net/Tcp.lean` over `Std.Internal.UV.TCP`): the phase 3
multistream/Noise/yamux/mplex exchanges all pass over loopback TCP
(`Tests/Tcp.lean`), where kernel segmentation provides the hostile
byte-stream semantics. Step 24 rebuilt the host around an upgrader
(`LeanP2P/Conn/Upgrade.lean`): security (`/noise`) and muxer
(`/yamux/1.0.0`, `/mplex/6.7.0`) are negotiated with multistream-select
on the wire, the handshake identity is verified against the dial target,
sessions are deduplicated per peer, dial-by-PeerId goes through the
peerstore, and `Host.addrs` reports listen addrs with the `/p2p/` suffix.
Two full hosts ping/identify/echo over loopback TCP (`Tests/Node.lean`).

Review follow-ups (2026-09-28): the upgrader now selects the muxer from
the Noise handshake extension with go's rule (initiator orders by its own
preference, responder follows the initiator; otherwise multistream
fallback), `Host.addrs` emits one `/p2p/`-encapsulated address per
listener, `/p2p/`-suffixed multiaddrs dial with the suffix as the
expected identity, and the toy `noise-sim` XOR was fixed into a
position-tracked stream cipher (per-chunk XOR desynced under TCP
coalescing). The step 24 done-criterion is now met for real:
`scripts/ping-interop.sh` builds a go-libp2p v0.50.0 node in docker and a
Lean node pings it and is pinged by it on loopback, both directions,
over `tcp + /noise + yamux` with extension-based muxer selection.

Status update 2026-09-30: **phase 5 steps 25-26 (harness + first matrix
rows) are implemented**. Step 25 is the transport-interop harness in
test-plan shape: the `interop` exe reads `transport`, `muxer`,
`security`, `is_dialer`, `ip`, `redis_addr`, `test_timeout_seconds`; the
listener `RPUSH`es its multiaddr on `listenerAddr`, the dialer `BLPOP`s
it, pings once and prints `{"handshakePlusOneRTTMillis": ..,
"pingRTTMilllis": ..}` (keys verbatim, typo included). The Redis side is
a minimal RESP2 client over the Lean TCP transport
(`LeanP2P/Interop/Redis.lean`); `scripts/interopd.go` is the go-libp2p
v0.50 counterpart reading the same environment; `interop/leanp2p/`
(Dockerfile + Makefile emitting the upstream `image.json`) drops into a
`libp2p/test-plans` fork as `impl/leanp2p/<v>/` and was verified live (lean container as
listener, go container dialing it through Redis on a docker network).
Step 26 fixed every interop blocker phase 4 had recorded before running
the cells: mplex stream identity now follows go-mplex (both sides count
from zero, the Receiver/Initiator flag keys the stream, so simultaneous
same-id streams coexist); yamux acknowledges accepted streams (spec:
ACK or RST), opens with an empty SYN window update (go semantics),
bounds sends by the peer's WindowUpdate credit and returns consumed
bytes as half-window credit; simultaneous dials resolve go-style (both
sides keep the connection dialed by the smaller peer id); TCP write
failures tear the connection down; all yamux frame writes serialize on
the session mutex (the pump's new ACK writes raced handler writes at the
Noise layer). The stress also exposed two latent bugs, both fixed:
`BufReader.readExactly` re-served its buffer (any leftover ≥ the request
duplicated bytes — the framing desynced), the echo handler did not
propagate EOF, the same double-serve existed in the redis client's line
reader, and yamux counted received bytes twice as window credit. A
post-implementation review round then reshaped the yamux pump (control
frames queue through a dedicated writer task, so the pump never blocks
on the write mutex), restricted the dial resolution to genuine races
(direction + freshness window — a later inbound connection no longer
displaces a healthy session), and made the harness test-plans compatible
in the details: `redis_addr` resolves DNS names (getaddrinfo in the C
shim, so the compose default `redis:6379` works) and a listener given
the runner default `ip=0.0.0.0` advertises the interface address its
redis connection used. Both were verified with a fully containerized
cell (lean image as listener with `ip=0.0.0.0` + `redis_addr=redis:6379`,
a go container dialing it through the service name). Done criteria: `Tests/Interop.lean` (same-id mplex
streams with no cross-delivery; a 1 MiB round trip — 4× the initial
yamux window — both directions over noise-encrypted TCP; three rounds of
simultaneous dials converging to one usable connection per side), and
the live matrix `scripts/interop-matrix.sh`: **tcp × noise × yamux,
lean ↔ go-libp2p v0.50, both dial directions, green through Redis** (the
mplex cells are reported as not-runnable against go v0.50 — mplex was
removed upstream; the Lean side's go-compatible mplex is covered
in-process). `suite passes under +RTS -N1`: 3119 checks, 0 failed. The
nightly workflow runs the go cells. Remaining phase 5: the
`tcp × tls × yamux` and `ws × noise × yamux` rows (TLS 1.3 transport,
WebSocket transport), the rust/js/nim columns (same harness), and steps
27-28 (QUIC/WebTransport/WebRTC via a backend; hole-punch/perf).
Phase 5 (the wider interop matrix, ws, QUIC, hole-punch/perf) remains
open in those parts, with the mplex-identity, yamux-flow-control,
simultaneous-dial and write-error items now closed.

## 1. What "the vector tests of libp2p" are

libp2p has no single vector suite. The tests that matter are spread over
several repositories. This plan targets all of them, in three tiers:

| Tier | Suite | Where it lives | Kind |
|---|---|---|---|
| A | unsigned-varint | `multiformats/unsigned-varint` README | spec examples + rules |
| A | multibase | `multiformats/multibase/tests/*.csv` | CSV vectors |
| A | multihash | `multiformats/multihash` README (`"multihash"` vectors, sha1 + sha2-256, hex/base32/base58/base64) | spec examples |
| A | multiaddr, Go tables | `multiformats/go-multiaddr/multiaddr_test.go` (TestConstructSucceeds, TestConstructFails, TestStringToBytes, TestBytesToString, TestEqual, TestGetValue, TestEncapsulate, TestDecapsulate, TestInvalidP2PAddrBytes/String, TestZone, TestHTTPPath, TestDNS, marshaler tests, fuzz round-trips) | Go test tables |
| A | multiaddr, JS suite | `multiformats/js-multiaddr/test/index.spec.ts` (construction, variants, normalize, getComponents, decapsulate, decapsulateCode, equals, unknown protocols) | TS test tables |
| A | multiaddr protocol table | `multiformats/multiaddr/protocols.csv` | authoritative codes |
| B | peer-ids and keys | `libp2p/specs/peer-ids/peer-ids.md` (key protobuf, identity inlining, base58 and CIDv1 forms, example ids) + go-libp2p `core/crypto` and `core/peer` test data | spec examples + impl tests |
| B | TLS certificate extension | `libp2p/specs/tls/tls.md` "Test vectors" (4 certs: Ed25519, ECDSA, secp256k1 valid; one ECDSA invalid) | spec vectors |
| B | Noise XX | `libp2p/specs/noise` (no vectors) + Noise framework vectors for `Noise_XX_25519_ChaChaPoly_SHA256` (`cacophony` / `snow` vector files) | framework vectors |
| B | multistream-select | spec README examples (`na`, `ls`, header, `ls` reply framing) | spec examples |
| B | signed envelopes and peer records | `libp2p/specs/RFC/0002`, `RFC/0003` (no vectors) + go-libp2p / rust-libp2p envelope tests | impl tests |
| B | yamux, mplex framing | hashicorp yamux spec, `libp2p/specs/mplex` | spec examples, interop |
| C | transport interop | `libp2p/test-plans/transport-interop` (dialer/listener, Redis coordination, ping, JSON timing output) | live interop with go/rust/js |
| C | hole-punch and perf interop | `libp2p/test-plans` | live interop |

Tier A is pure codecs and is the cheapest. Tier B needs real crypto and
protobuf. Tier C needs real sockets and a matching node harness.

## 2. Gap analysis against the current code

### 2.1 Passing now

- uvarint round trip (theorem) and one explicit vector.
- multiaddr: 18 protocols, Go `TestStringToBytes` subset (3), JS variants
  subset (21), JS normalize (7), 9 invalid inputs.
- SHA-256 (NIST + spec), multihash sha2-256 and identity, base58btc.
- multistream-select wire examples and a two-party exchange in the sim.

### 2.2 Missing or wrong, per layer

**Varint** (`Net/Varint.lean`)
- Accepts non-minimal encodings (`[0x81, 0x00]` decodes to 1). The spec says
  reject.
- No 9-byte / 63-bit limit. The spec says implementations MUST enforce it.
- Works only on `List Nat`; no `ByteArray` entry point for the IO edge.

**Multibase** (does not exist)
- Needed by: CIDv1 peer ids (base32, base36), `certhash` (multibase
  multihash), `onion` / `onion3` (base32), `garlic32` (base32, no padding),
  `garlic64` (i2p base64 alphabet), the multihash README vectors
  (base32 / base64 forms).

**Multihash / CID** (`Crypto/Multihash.lean`)
- No validation when decoding: length mismatch, unknown code, trailing bytes.
- No sha1 (needed only for the README vector; can be table-driven).
- No CID type. Peer ids in `bafz...` (CIDv1 + `libp2p-key` 0x72 + base32)
  form cannot be parsed or printed.
- `Base58.decode?` does not check that the result is a valid multihash. The
  Go tests `TestInvalidP2PAddrBytes` and `TestInvalidP2PAddrString` require
  rejection of `/p2p/QmxoHT6iViN5xAjoz1VZ553cL31U9F94ht3QvWR1FrEbZY`
  (declared digest length does not match).

**Multiaddr** (`Net/Multiaddr.lean`)
- Protocol table: 18 of 42 rows of `protocols.csv`. Missing: `dccp` 33,
  `ip6zone` 42, `ipcidr` 43, `sctp` 132, `udt` 301, `unix` 400, `onion` 444,
  `onion3` 445, `garlic64` 446, `garlic32` 447, `sni` 449, `noise` 454,
  `webtransport` 465, `certhash` 466, `http-path` 481, `p2p-websocket-star`
  479, `p2p-stardust` 277, `p2p-webrtc-star` 275, `p2p-webrtc-direct` 276,
  `webrtc-direct` 280, `webrtc` 281, `memory` 777, `ech` 9849.
- Path protocols (`unix`, `http-path`) consume the rest of the string and
  are percent-encoded. The current parser takes exactly one segment.
- Fixed-size non-IP values: `ipcidr` (1 byte), `onion` (10 bytes + u16
  port), `onion3` (35 bytes + u16 port), `memory` (u64 big endian).
- `ip6zone` text form `x%y` and the rule "zone must be followed by ip6".
- Value validation in the binary decoder is weak (any 4 bytes is an ip4,
  no check that a `p2p` value is a well-formed multihash, no check of
  minimal varint, no size limits). `FuzzNewMultiaddrBytes` needs the
  decoder to be total and to reject the same inputs Go rejects.
- No operations API: `encapsulate`, `decapsulate` (last occurrence),
  `decapsulateCode`, `split` / `join`, `getValue`, `protocols`, component
  view, `Equal`, JSON / text / binary marshalers, `isThinWaist`, `Contains`,
  `UniqueAddrs`, `FilterAddrs`. The Go and JS suites test all of these.
- The multiaddr model is `List Nat` all the way. Real code needs
  `ByteArray` with a thin proof-facing view.
- IPv4-mapped IPv6 printing (`::ffff:1.2.3.4`) differs between Go (dotted)
  and JS (hex). Decide per suite and encode the decision in the tests.

**Keys and PeerId** (`Crypto/PeerId.lean`)
- Keys are seed strings. No Ed25519, secp256k1, ECDSA P-256, RSA.
- No `PublicKey` / `PrivateKey` protobuf (`KeyType` enum 0..3, `Data`).
- PeerId is always sha2-256. The spec inlines keys that serialize to at most
  42 bytes with the identity multihash (so every Ed25519 id is `12D3KooW...`).
- No CIDv1 string form, no `16Uiu2HA...` (secp256k1) shape check.
- No signing / verification, so nothing in tier B can be tested.

**Protobuf** (does not exist)
- Needed by keys, identify, Noise handshake payload, envelopes, peer
  records, and every later protocol (kad, pubsub, autonat, relay).

**Hashing and ciphers** (`Crypto/Sha256.lean`)
- SHA-256 over `List Nat` is fine for vectors, too slow for traffic.
- Missing: SHA-512 (Ed25519), HMAC-SHA256, HKDF (Noise), X25519,
  ChaCha20-Poly1305, SHA-1 (multihash vector only).

**multistream-select** (`Protocol/Multiselect.lean`)
- `ls` reply is not implemented (reply is one length-prefixed message whose
  body is a list of length-prefixed protocol names, each ending in `\n`).
- `readMsg` assumes one message per `read`. Real streams split and coalesce
  bytes. Needs a buffered reader.
- No max message length (implementations cap at 1024 bytes and reject).
- No lazy / optimistic negotiation (`V1Lazy` in Go), which Go dialers use.
  The listener side must cope with the header and first proposal arriving
  in one write.

**Security** (`Conn/Security.lean`)
- Toy XOR. Need Noise XX (`Noise_XX_25519_ChaChaPoly_SHA256`, 2-byte
  big-endian length framing, 65535 max, `NoiseHandshakePayload` protobuf,
  signature prefix `noise-libp2p-static-key:`, extensions with muxer list).
- TLS 1.3 with the libp2p extension (OID `1.3.6.1.4.1.53594.1.1`, prefix
  `libp2p-tls-handshake:`, ALPN `libp2p`). The four spec vectors only need
  X.509 parsing, extension extraction and signature verification, not a
  full TLS stack.

**Muxer** (`Conn/Mux.lean`)
- Custom `[sid u32le][len u32le]` framing. Nobody else speaks it. Need
  yamux (12-byte big-endian header: version, type, flags, stream id,
  length; SYN/ACK/FIN/RST; 256 KiB window with `WindowUpdate`; ping;
  GoAway) and/or mplex (uvarint header `id << 3 | flag`, uvarint length,
  1 MiB max).
- No flow control, no reset semantics beyond a closed pipe, no keepalive.

**Protocols** (`Protocol/Ping.lean`, `Protocol/Identify.lean`)
- Ping id must be `/ipfs/ping/1.0.0`; payload is 32 random bytes; responder
  echoes until the stream closes; dialer loops.
- Identify id must be `/ipfs/id/1.0.0` (+ `/ipfs/id/push/1.0.0`); message is
  the `Identify` protobuf (protocolVersion, agentVersion, publicKey,
  listenAddrs, observedAddr, protocols, signedPeerRecord).
- Signed envelopes (RFC 0002) and peer records (RFC 0003, payload type
  `0x0301`, domain `libp2p-peer-record`) are absent.

**Transport, host, concurrency** (`Sim.lean`, `Host.lean`, `Conn/Mux.lean`)
- Only the in-memory sim. Interop needs TCP at minimum; QUIC, WebSocket,
  WebTransport, WebRTC later.
- Polling loops with `IO.sleep 1`, non-atomic `IO.Ref` read-modify-write,
  no mutex, no channel, no promise-based wake. Not safe under real load.
- Host has no dial by PeerId, no connection dedup, no protocol negotiation
  for security / muxer (libp2p negotiates `/noise`, `/tls/1.0.0`,
  `/yamux/1.0.0`, `/mplex/6.7.0` with multistream-select on the raw
  connection, or takes them from the multiaddr).

## 3. Step-by-step plan

Each step names the upstream test that defines "done". Steps inside one
phase are independent unless stated. Keep the spike's rule: a pure module
with a round-trip theorem first, the IO shell after.

### Phase 0: test infrastructure

1. **Vendor the vector sources.** Add `vendor/` git submodules (or pinned
   copies with the commit hash in a `VECTORS.lock`): `multiformats/multiaddr`,
   `multibase`, `unsigned-varint`, `multihash`, `go-multiaddr`,
   `js-multiaddr`, `libp2p/specs`, `libp2p/test-plans`.
2. **Convert tables to JSON.** Write one script (`scripts/extract-vectors.*`)
   that turns the Go and TS test tables into `Tests/vectors/*.json`. Commit
   the JSON and the script. Hand-copied vectors, as now, do not scale to
   several hundred entries.
3. **Test runner.** Replace the single `Tests/Main.lean` with one module per
   suite (`Tests/Varint.lean`, `Tests/Multiaddr.lean`, ...), a shared
   `check` helper, JSON loading via `Lean.Json`, and a summary that names the
   upstream file each suite mirrors. Add `lake test`.
4. **CI.** Build and run on every push. Add a nightly job for the interop
   suite later (phase 5).

### Phase 1: multiformats codecs (tier A)

5. **Varint conformance.** Reject non-minimal encodings, enforce the 9-byte
   limit, add a `ByteArray` decoder that reports bytes consumed. Prove
   `decode (encode n) = n` still, and add a theorem that `decode` on a
   non-minimal input returns `none`. Done: all README examples, plus
   negative cases `[0x81,0x00]` and a 10-byte input.
6. **Multibase.** `Multibase.encode : Base → ByteArray → String` and
   `decode? : String → Option (Base × ByteArray)` for identity, base2, base8,
   base10, base16 (both cases), base32 (lower/upper, pad/no-pad, hex
   variants), base36, base58btc, base58flickr, base64, base64pad, base64url,
   base64urlpad. Done: the four CSV files in `multibase/tests` pass in both
   directions, including leading-zero and case-insensitivity files.
7. **Multihash and CID.** Table-driven multihash with `decode?` that
   validates code, declared length, and consumes exactly. Add sha1 for the
   README vector. Add `Cid` (v0 = bare sha2-256 multihash, v1 =
   `0x01 <codec> <multihash>`) with multibase string forms. Done: multihash
   README vectors in hex/base32/base58/base64; `bafzbeie5...` <-> `QmYyQSo...`
   round trip from the peer-ids spec.
8. **Multiaddr, full protocol table.** Regenerate the `AddrComponent` type
   and `code` / size tables from `protocols.csv`. Add every missing
   protocol, with these value codecs:
   - fixed: `dccp`, `sctp` (u16), `ipcidr` (u8), `memory` (u64 BE),
     `onion` (10 B + u16), `onion3` (35 B + u16);
   - varint-length: `ip6zone`, `unix` (path, percent-decoded), `sni`,
     `http-path` (path, percent-decoded), `garlic64` (i2p alphabet,
     >= 386 B), `garlic32` (base32 nopad, >= 35 B), `certhash` (multibase
     multihash);
   - size 0: `udt`, `noise`, `webtransport`, `webrtc`, `webrtc-direct`,
     `p2p-webrtc-star`, `p2p-webrtc-direct`, `p2p-websocket-star`,
     `p2p-stardust`, `ech`.
   Move the wire model to `ByteArray` with a `List Nat` view used only in
   proofs. Done: `TestConstructSucceeds`, `TestConstructFails`,
   `TestStringToBytes`, `TestBytesToString`, `TestZone`, `TestHTTPPath`,
   `TestDNS`, `TestIPFSvP2P`, `TestInvalidP2PAddr*`, and the full JS
   `variants`, `normalize`, `invalid`, `unknown protocols` suites.
9. **Multiaddr operations API.** `encapsulate`, `decapsulate` (last match),
   `decapsulateCode`, `split` / `join`, `components`, `protocols`,
   `valueForProtocol`, `Equal`, `Contains`, `UniqueAddrs`, `FilterAddrs`,
   JSON / text / binary marshal and unmarshal. Done: `TestEncapsulate`,
   `TestDecapsulate*`, `TestGetValue`, `TestEqual`, `TestProtocols*`,
   `TestBytesSplitAndJoin`, `Test*Marshaler`, `TestFilterAddrs`,
   `TestContains`, `TestUniqueAddrs`; JS `getComponents`, `decapsulate`,
   `decapsulateCode`, `equals`, `construction`.
10. **Decoder totality.** Port the Go fuzz corpus (`FuzzNewMultiaddrBytes`,
    `FuzzNewMultiaddrString`, `FuzzSplitRoundtrip`) as a property test:
    every accepted byte string round-trips, every accepted text string
    round-trips, and decoding never panics. Prove
    `decode (encode c) = some c` for every component kind, not only the
    four covered today.

### Phase 2: crypto and protobuf (foundation for tier B)

11. **Crypto backend decision.** Constant-time Ed25519, X25519,
    ChaCha20-Poly1305 and RSA are not sensible to write in Lean for a
    production node. Recommended: `extern` bindings to libsodium (Ed25519,
    X25519, ChaCha20-Poly1305, SHA-512, HMAC, random) and to OpenSSL or
    BoringSSL for secp256k1, ECDSA P-256, RSA, X.509 and TLS 1.3. Keep the
    pure Lean SHA-256 as the reference used in proofs and tests. Record the
    decision in the README.
12. **Protobuf wire codec.** A pure encoder / decoder for varint, fixed64,
    length-delimited and fixed32 fields, with unknown-field skipping and a
    round-trip theorem, plus a small derive-style helper for message
    structures. Done: encode / decode of `PublicKey`, `PrivateKey`,
    `Identify`, `NoiseHandshakePayload`, `Envelope`, `PeerRecord` against
    bytes produced by go-libp2p (capture them once with a Go script and
    commit as vectors).
13. **Keys and PeerId.** `KeyType` 0..3, marshal / unmarshal for each key
    type (Ed25519 raw 32 B, secp256k1 33 B compressed, ECDSA and RSA DER),
    signing and verification, and `PeerId.ofPublicKey` with the 42-byte
    identity inlining rule. String forms: base58btc multihash and CIDv1
    `libp2p-key` base32 / base36; parsing accepts both and validates the
    multicodec. Done: the three example ids in the peer-ids spec, go-libp2p
    `core/crypto` key test data (RFC 8032 Ed25519 vectors, secp256k1 and
    ECDSA sign/verify), `core/peer` id tests (`Decode`, `Encode`, `ToCid`,
    `FromCid`, `IDFromPublicKey`).
14. **Hash and KDF set.** SHA-512, HMAC-SHA256, HKDF-SHA256 with RFC 5869
    vectors; SHA-256 over `ByteArray` with the existing `List Nat` version
    as the proof reference.

### Phase 3: wire protocols (tier B)

15. **multistream-select, complete.** Buffered message reader over a byte
    stream, `ls` reply, 1024-byte cap, listener that handles coalesced
    header + proposal, dialer lazy mode. Done: spec examples including the
    `ls` reply; a test where the sim splits every write into single bytes;
    interop with go-libp2p's `msio` captured traces.
16. **Noise XX.** Handshake state machine (`Noise_XX_25519_ChaChaPoly_SHA256`),
    cipher state with 64-bit nonce, 2-byte BE length framing, 65535 cap,
    handshake payload protobuf with signature prefix
    `noise-libp2p-static-key:`, muxer-negotiation extension. Done: Noise
    framework XX vectors (`cacophony.txt` entries for this suite, with
    prologue and with/without payloads) and an in-process handshake with a
    captured go-libp2p transcript.
17. **TLS certificate extension.** X.509 DER parsing (or via the backend),
    extension OID lookup, `SignedKey` ASN.1 decode, signature check over
    `"libp2p-tls-handshake:" ++ SPKI`, peer id derivation. Done: the four
    vectors in `tls.md` (three valid with expected ids, one invalid). Full
    TLS 1.3 handshake goes through the backend with ALPN `libp2p`.
18. **yamux.** Header codec with a round-trip theorem, stream state machine
    (SYN / ACK / FIN / RST), receive window and `WindowUpdate`, ping,
    GoAway, odd ids for the initiator, `/yamux/1.0.0`. Done: frame codec
    unit vectors, a two-party test over a byte-splitting sim, then the
    interop matrix in phase 5.
19. **mplex.** Header codec (`id << 3 | flag`), the seven flags, 1 MiB
    cap, `/mplex/6.7.0`. Same done criteria as yamux. Optional if yamux is
    enough for the interop matrix; go and rust still ship it.
20. **Ping and Identify to spec.** `/ipfs/ping/1.0.0` with 32-byte random
    payload loop; `/ipfs/id/1.0.0` and `/ipfs/id/push/1.0.0` with the
    `Identify` protobuf, observed address, protocol list. Done: protobuf
    vectors from step 12, and a sim test where the responder id is derived
    from the identify public key and matches the Noise remote id.
21. **Signed envelopes and peer records.** RFC 0002 signature input
    (varint-length-prefixed domain, payload type, payload), RFC 0003
    `PeerRecord` with seq and addresses, payload type `0x0301`, domain
    `libp2p-peer-record`. Done: envelopes produced by go-libp2p verify;
    envelopes produced here verify in go-libp2p (script in `scripts/`).

### Phase 4: real node

22. **Concurrency core.** Replace polling queues with `IO.Promise`,
    `Std.Mutex` / `Std.Channel` (or a single-owner event loop per
    connection as the README recommends). Every task has an owner and is
    joined on close. Done: the existing sim tests pass with `+RTS -N1`
    (no starvation) and under a stress test with 1000 streams.
23. **TCP transport.** Use Lean's async socket API if the toolchain
    provides it (check `Std.Internal.UV` / `Std.Net` in v4.34), otherwise
    `extern` to libuv or POSIX. Byte-stream semantics: reads return any
    prefix, writes may split. Done: the multistream, Noise, yamux tests
    from phase 3 pass over loopback TCP.
24. **Upgrader and host.** Negotiate security (`/noise`, `/tls/1.0.0`) and
    muxer (`/yamux/1.0.0`, `/mplex/6.7.0`) with multistream-select on the
    raw connection, or take them from the multiaddr (`/tls`, `/noise`).
    Dial by PeerId through the peerstore, verify the remote id after the
    handshake, deduplicate connections, expose `listenAddrs` with `/p2p/`
    suffix. Done: a Lean node pings a go-libp2p node and vice versa on
    loopback.

### Phase 5: interop (tier C)

25. **transport-interop harness.** A `lean_exe interop` that reads
    `transport`, `muxer`, `security`, `is_dialer`, `ip`, `redis_addr`,
    `test_timeout_seconds`; listener does `RPUSH listenerAddr`, dialer does
    `BLPOP`, pings, prints `{"handshakePlusOneRTT":..,"pingRTT":..}`.
    Needs a minimal Redis RESP client. Add a `Dockerfile` and an
    `image.json`-emitting Makefile in a fork of `libp2p/test-plans`.
26. **Interop matrix, in this order:** `tcp × noise × yamux`,
    `tcp × noise × mplex`, `tcp × tls × yamux`, `ws × noise × yamux`.
    Run against go-libp2p, rust-libp2p, js-libp2p, nim-libp2p. Done: green
    for every pair in the matrix.
27. **QUIC, WebTransport, WebRTC.** Only through a backend (msquic or
    quiche via FFI). Schedule after the TCP matrix is green. Each adds a
    row to the interop matrix; `quic-v1` needs no muxer or security row.
28. **hole-punch and perf suites.** Need AutoNAT, circuit relay v2 and
    DCUtR (all protobuf-based, so phase 2 makes them cheap to add). Perf
    needs the `/perf/1.0.0` protocol. These have no vectors; interop is
    the only test.

## 4. Suggested order and effort

| Order | Steps | Unlocks | Rough size |
|---|---|---|---|
| 1 | 1-4 | everything | small |
| 2 | 5-10 | all tier A suites | medium; multiaddr is the bulk |
| 3 | 11-14 | all tier B suites | medium, mostly binding work |
| 4 | 15-21 | spec conformance of the stack | large |
| 5 | 22-24 | a node that talks to others | large; concurrency is the risk |
| 6 | 25-28 | tier C | medium, then grows per transport |

Tier A can be finished without touching IO or crypto and gives the most
vectors per hour. Tier B cannot start before step 11 is decided.

## 5. Decisions to make before starting

- **Crypto: FFI or pure Lean.** Recommendation: FFI (step 11). Pure Lean
  is acceptable for hashes and for reference implementations used in proofs.
- **Byte model.** Move production code to `ByteArray`; keep `List Nat`
  (or move to `BitVec 8`) only inside proofs, with one conversion lemma set
  in `Crypto/Bytes`.
- **IPv4-mapped IPv6 text form.** Pick Go's dotted form or JS's hex form
  and mark the other suite's cases as expected divergences.
- **Muxer priority.** yamux first; mplex only if the interop matrix needs
  it.
- **Vector provenance.** Every vector file records the upstream repository,
  path and commit hash.

## 6. Known bugs in the spike that the vectors will expose first

- `Varint.decode?` accepts non-minimal encodings and unbounded length.
- `Multiaddr.decodeBinF` accepts any bytes as a `p2p` value; no multihash
  validation.
- `PeerId.derive` never uses identity inlining, so Ed25519 ids would be
  wrong (`Qm...` instead of `12D3KooW...`).
- `Multiselect.readMsg` and `Stream.readLine` assume message boundaries
  that real transports do not preserve.
- `Pipe.push` / `Pipe.read` and every `IO.Ref` list update are
  read-modify-write without a lock.
