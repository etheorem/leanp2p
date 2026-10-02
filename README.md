# leanp2p — a Lean 4 spike of libp2p

A throwaway prototype of libp2p's core architecture in Lean 4, built to
**inform the architecture of a real implementation**, not to be one.
Everything runs end-to-end: two hosts dial over loopback TCP, negotiate
`/noise` with multistream-select, authenticate identities with the real
Noise XX handshake, pick the muxer from the Noise extensions, mux
streams, and run ping / identify / echo (phase 4) - the node pings a
real go-libp2p node, both directions (`scripts/ping-interop.sh`), and
the phase 5 transport-interop harness runs the test-plan-shaped cells
(`scripts/interop-matrix.sh`: tcp × noise × yamux against go-libp2p
through Redis, both dial directions). The deterministic in-memory sim
remains as the conformance/stress harness.

```bash
lake build
./.lake/build/bin/demo +RTS -N8 -RTS   # end-to-end demo (TCP loopback; see "Concurrency")
lake test                              # vector suites (see "Vector test harness" below)
```

## Layout (mirrors libp2p layering)

```
Crypto/Bytes        byte/hex/xor helpers, toy FNV (IO boundary)
Crypto/Hash         HashAlgorithm class (real impl would bind sha256/blake2b)
Crypto/Sha256       SHA-256, pure `List Nat` core + ByteArray entry point
Crypto/Sha512       SHA-512, pure (phase 2; Ed25519/Noise need it)
Crypto/Hmac         HMAC-SHA-256 (RFC 2104, pure)
Crypto/Hkdf         HKDF-SHA-256 (RFC 5869, pure)
Crypto/OpenSsl      OpenSSL 3 FFI: Ed25519, X25519, secp256k1, ECDSA P-256,
                    RSA, random, digests/hmac/hkdf cross-checks
Crypto/Pb           protobuf wire codec, VERIFIED round trip (phase 2)
Crypto/Keys         KeyType, deterministic key protobufs, sign/verify,
                    PeerId.ofPublicKey (identity inlining) + text forms
Crypto/Messages     Identify, NoiseHandshakePayload, Envelope, PeerRecord
Conn/Noise          Noise XX (Noise_XX_25519_ChaChaPoly_SHA256), verified codec
Conn/TlsExt         TLS certificate extension (tls.md vectors)
Conn/Yamux          yamux multiplexer: 12-byte header codec + state machine
Conn/Mplex          mplex multiplexer: varint header codec + 1 MiB cap
Conn/Reader         Buffered byte reader (over any Connection)
Conc                phase 4 concurrency core: Chan (blocking FIFO), TaskSet,
                    mutex-guarded cells (no polling, no racy IO.Ref)
Crypto/PeerId       PubKey -> multihash-shaped PeerId, derived via the hash interface
Net/Multiaddr       AddrComponent/Multiaddr + VERIFIED binary codec + text form
Net/Tcp             phase 4 TCP transport over Std.Internal.UV.TCP
Net/Transport       Connection / Listener / Transport  (structure-based interfaces)
Conn/Frame          muxer frame codec  [sid u32le][len u32le][payload]  VERIFIED
Conn/Stream         Stream: what application protocols see
Conn/Security       SecurityProtocol + SecureConn, toy "noise-sim" impl
Conn/Upgrade        phase 4 upgrader: security + muxer negotiation, Session
Conn/Mux            Pipe, MuxSession, Muxer (yamux-style odd/even stream ids, EOF = empty frame)
Peer/Peerstore      addrs + keys by PeerId
Protocol/Multiselect  pure negotiation core (PROVEN) + wire helpers
Protocol/Ping       /ipfs/ping/1.0.0: 32-byte echo + RTT
Protocol/Identify   /ipfs/id/1.0.0: Identify protobuf + peer-id derivation
Sim                 in-memory transport (deterministic test harness)
Host                dial/accept pipelines: transport -> security -> mux -> multiselect -> handler
Interop/Redis       phase 5 RESP2 client for the transport-interop harness
Interop             phase 5 harness exe (test-plans shape; scripts/interop-matrix.sh)
PingNode            phase 4 interop node (go-libp2p loopback ping, scripts/ping-interop.sh)
```

## Machine-checked properties

| File | Theorem | Meaning |
|---|---|---|
| `Net/Varint` | `decode_encode`, `decode_encode_app` | uvarint roundtrips, also against a longer buffer |
| `Conn/Frame` | `decode_encode` | decoding a serialized frame recovers it and consumes exactly the buffer |
| `Protocol/Multiselect` | `choose_spec` | a negotiated protocol is supported by both sides |
| `Net/Varint` | `decode_encode_inv` | a decoded varint is exactly the encoding of its value (minimality + self-delimiting) |
| `Crypto/Pb` | `decode_encode`, `decode_encode_fields` | protobuf round trip: decoding an encoding recovers the fields and consumes exactly the buffer (phase 2) |

(The multiaddr binary codec now carries its own round-trip theorems for the
value-less, port, tcp/udp component kinds — see `Net/Multiaddr` — while the
string-transcoded kinds are anchored by the official vectors and the fuzz
property tests below.)

## Vector test harness (phase 0) + multiformats codecs (phase 1)

The hand-copied vectors of the spike are replaced by an extraction pipeline
(VECTOR_TEST_PLAN.md, phase 0), and phase 1 (steps 5-10) implemented the
full tier-A multiformats codec layer against them:

- **`VECTORS.lock` + `vendor/`** — pinned byte-exact copies of the upstream
  sources: `multiformats/{multiaddr,multibase,unsigned-varint,multihash}`,
  `go-multiaddr`, `js-multiaddr`, `libp2p/{specs,test-plans}`.
  Recreate with `scripts/vendor-pull.sh`; verify with
  `scripts/vendor-pull.sh --verify`.
- **`scripts/extract-vectors.py`** — turns the upstream Go/TS test tables,
  CSVs and spec-README examples into `Tests/vectors/*.json`. Every file
  records its provenance (`repo`, `commit`, `path`, `upstreamTest`) in a
  `_provenance` field. Re-run it after bumping a pin and commit the JSON.
- **`Tests/`** — one module per suite (`Varint`, `Multibase`, `Multihash`,
  `Multiaddr`, `MultiaddrOps`, `Multiselect`, `Spike`), each naming the
  upstream file it mirrors, loading vectors via `Lean.Json`, with a shared
  `Runner` in `Tests/Support.lean`. Run with `lake test`; exit code is
  nonzero only on real failures.

Phase 1 status (steps 5-10, all done):

| step | what | where |
|---|---|---|
| 5 | varint conformance: minimal encodings only, 9-byte cap, `ByteArray` decoder reporting bytes consumed; `decode_encode`, `decode_encode_inv`, `decode_nonminimal`, `decode_too_long` theorems | `Net/Varint` |
| 6 | full multibase: identity, base2/8/10, base16 (both cases), base32 family incl. hex/pad/z, base36, base58btc/flickr, base64 family, base256emoji; the four upstream CSVs pass in both directions (case-insensitivity file: decode direction, its values are non-canonical) | `Crypto/Multibase` |
| 7 | table-driven multihash with strict `decode?` (known code, exact digest length, no trailing bytes), sha1 for the README vector, CIDv0/CIDv1 with `libp2p-key` text forms; `Qm...` <-> `bafz...` round trip | `Crypto/Multihash`, `Crypto/Cid`, `Crypto/Sha1` |
| 8 | full protocols.csv table (42 rows) with the upstream value codecs: onion/onion3 (base32 host + port), garlic64/32 (i2p alphabets, length rules), certhash (multibase multihash), ip6zone (adjacency to ip6), path protocols, p2p = base58 multihash or multibase CIDv1 with codec 0x72 | `Net/Multiaddr` |
| 9 | operations API: `encapsulate`, `decapsulate?` (Go semantics), `decapsulateThrow?` (js semantics), `decapsulateCode`, `split`/`join`, `getComponents`, `protocols`, `valueForProtocol?`, `equal`, `contains`, `uniqueAddrs`, `filterAddrs`, binary/text/JSON marshalers | `Net/Multiaddr` |
| 10 | decoder totality: `decodeBinF_nil`, `decodeBinF_tcp`, `decodeBin_encodeBin_tcp/udp/valueless` theorems plus LCG-driven fuzz property tests (random byte strings and random component sequences must round-trip) | `Net/Multiaddr`, `Tests/MultiaddrOps` |

Check kinds in the suites:

| kind | meaning |
|---|---|
| pass | vector holds |
| todo | known implementation gap; printed, does not fail CI (currently zero) |
| skipped | CSV/spec header rows that carry no testable vector (currently six) |

Current: 3119 passed, 0 failed, 0 todo, 4 skipped (2 js-only `memory`
vectors, 2 documented re-sign divergences) — 2775 from phases 0-1, 155
from phase 2, and 189 from phases 3-5 (wire protocols, the TCP transport
suites, the node/stress suites, and the phase 5 interop prereqs: go-mplex
identity, yamux flow control, simultaneous dials). Phase 1
closed every gap the phase-0 run had exposed:
varint minimality and the 9-byte cap, strict multihash validation (which
fixes the `TestInvalidP2PAddr*` vectors for the right reason),
multibase/CIDv1 p2p values, the IPv6 `::`/`::ffff:` printing rules, and the
full protocol table. Divergences between upstream implementations are
resolved and recorded in `Net/Multiaddr.lean`:

- p2p print form follows the parsed form (base58 or CIDv1 base32; Go always
  prints base58, js prints CIDs);
- `unix` keeps the Go verbatim bytes while `getComponents` reports the js
  decoded form; `unix` is terminal in the binary codec (no component may
  follow a path protocol, per go-multiaddr `readMultiaddr`);
- `memory` is a big-endian u64 (go/rust wire form; the CSV's `V` is stale).
  The two js vectors that use a string value are skipped as documented
  divergences;
- the empty address rejects like Go but prints `/` like js;
- IPv4-mapped IPv6 prints dotted like Go.

The wire codec itself (`encodeBinB` / `decodeBinB`) works directly on
`ByteArray` - encoding pushes bytes through a builder, decoding indexes
into the buffer. The `List Nat` functions are the proof-facing view: the
round-trip theorems are stated on them, and the fuzz property tests check
production/spec equivalence on every run
(`decodeBinB b == decodeBin (Bytes.toNatList b)`,
`encodeBinB cs == Bytes.ofNatList (encodeBin cs)`), so the two cannot
drift. (The ByteArray round-trip theorems themselves are not machine-checked
here: `ByteArray` ops do not kernel-reduce in this toolchain, so evaluation
proofs would not go through.)

Step 10 also ports Go's fuzz seed corpora
(`vendor/go-multiaddr/testdata/fuzz`, extracted into
`multiaddr-go-fuzz-{bytes,strings}.json`): decoding must be total, and every
accepted seed must round-trip through bytes and text. Beyond the corpus,
three fuzz sweeps run per test pass: pure random byte strings, valid
addresses with perturbed tails (complete or misaligned extra components),
and randomly generated component sequences - plus the production/spec
equivalence property on every input.

The first run of the extracted vectors caught two real SHA-256 bugs that the
hand-copied suite had missed (both single-block only): broken padding length
for messages ≥ 56 bytes (truncated `Nat` subtraction) and a missing chaining
value in `compress` (correct only for one block). Both fixed; NIST multi-block
vectors now pass.

CI (`.github/workflows/ci.yml`) builds and runs all of this on every push
and verifies that the vendored sources match `VECTORS.lock` and that the
committed JSON is reproducible; `.github/workflows/nightly.yml` reserves the
nightly slot for the tier C interop matrix (phase 5).

## Crypto backend decision (phase 2 step 11)

**Decision: OpenSSL 3 via a small C shim (`c/p2pcrypto.c`) for asymmetric
crypto; pure Lean for hashes/KDFs.** The plan's recommendation stands:
constant-time Ed25519/X25519/ChaCha20-Poly1305/RSA are not sensible to
write in Lean for a production node. libsodium was the other candidate but
is not available in this environment; OpenSSL covers Ed25519/X25519 *and*
the secp256k1 / ECDSA P-256 / RSA DER marshaling the peer-ids spec
requires. Asymmetric primitives (key derivation, sign, verify) bind to
OpenSSL through `@[extern]` opaque declarations in `Crypto/OpenSsl.lean`;
SHA-256/SHA-512, HMAC-SHA-256 and HKDF-SHA-256 are pure Lean
(`Crypto/Sha256`, `Crypto/Sha512`, `Crypto/Hmac`, `Crypto/Hkdf`) — they are
the reference implementations used in proofs — and every suite cross-checks
the pure versions against the OpenSSL backend at runtime so the two cannot
drift. Later phases pull X.509/TLS 1.3 and ChaCha20-Poly1305 from the same
backend. The shim compiles through Lake (`buildLeanO`) with the toolchain's
C compiler and links `libcrypto` by full path (the toolchain bundles its
own glibc; an extra `-L/usr/lib` would hijack `-lc`).

## Crypto and protobuf (phase 2)

Phase 2 (steps 11-14, all done) laid the tier-B foundation:

| step | what | where |
|---|---|---|
| 11 | OpenSSL 3 FFI shim + `@[extern]` bindings (Ed25519, X25519, secp256k1 with BIP-62 low-S DER, ECDSA P-256, RSA, random; SHA-256/512, HMAC, HKDF cross-checks); decision recorded above | `c/p2pcrypto.c`, `Crypto/OpenSsl` |
| 12 | protobuf wire codec (wire types 0/1/2/5, groups rejected, unknown fields kept) with the `decode_encode` round-trip theorem; deterministic encoders per the peer-ids spec; message structures Identify / NoiseHandshakePayload / Envelope / PeerRecord with RFC 0002/0003 signature input and self-certified peer records | `Crypto/Pb`, `Crypto/Messages` |
| 13 | `KeyType` 0..3, deterministic `PublicKey`/`PrivateKey` protobufs, per-type `Data` marshaling (Ed25519 raw, secp256k1 compressed, ECDSA SPKI/PKCS#8, RSA SPKI/PKCS#1), sign/verify dispatch, `PeerId.ofPublicKey` with the 42-byte identity-inlining rule, base58btc and CIDv1 `libp2p-key` (base32 emitted, base36 accepted) text forms | `Crypto/Keys` |
| 14 | pure SHA-512 (FIPS 180-4), HMAC-SHA-256 (RFC 2104/4231), HKDF-SHA-256 (RFC 5869), SHA-256 `ByteArray` entry point; every primitive cross-checked against OpenSSL on a padding-boundary sweep | `Crypto/Sha512`, `Crypto/Hmac`, `Crypto/Hkdf`, `Crypto/Sha256` |

Vectors: the go-libp2p key fixtures (`keys-go-libp2p.json`,
`vendor/go-libp2p/core/crypto/test_data` — the exact bytes go-libp2p's own
`TestFixtures` uses: RSA/secp256k1/ECDSA key protobufs plus signatures
over a fixed message), key protobufs from the peer-ids spec
(`keys-peer-ids.json`), RFC 8032 §7.1 Ed25519 (`keys-rfc8032.json`), and
RFC 4231/5869/FIPS examples (`hashes-rfc.json`). The fixture suite mirrors
upstream `TestFixtures`: marshal round trips, pubkey-from-priv, fixture
signature verification, and (RSA, where PKCS1-v1_5 is deterministic)
byte-identical re-signing.

Open items recorded from phase 2:

- step 12 message vectors (Identify / NoiseHandshakePayload / Envelope /
  PeerRecord) are self-generated from the spec field tables by an
  independent encoder (`protobuf-messages.json`) — internal-consistency
  evidence, not compatibility. To be replaced with bytes captured from a
  real Go node once one exists (phase 5 interop).
- secp256k1 re-signing is randomized in our OpenSSL backend; go's btcec
  signs deterministically (RFC 6979). The fixture signature still
  verifies and our re-signatures verify against go's public keys, but
  byte-level determinism needs RFC 6979 in the shim (phase 3, Noise).

The OpenSSL runtime cross-checks caught three real bugs during
development (all would have broken interop later): a truncated-`Nat`
subtraction in the SHA-512 padding length (exposed by a size sweep at
`l % 128 > 111`), a missing re-padding in HMAC key normalization for keys
longer than the block, and a forgotten multihash wrapper in the sha2-256
branch of `PeerId.ofPublicKey`. The `@& USize` FFI marshaling rule (plain
`Nat` is boxed) is worth remembering for every future extern.

## Wire protocols (phase 3)

Phase 3 (steps 15-21) delivered the tier-B wire protocol stack:

| step | what | where |
|---|---|---|
| 15 | multistream-select complete: buffered reader, 1024-byte cap, `ls` reply, lazy dialer, byte-split two-party tests, go-multistream captured traces | `Protocol/Multiselect`, `Conn/Reader`, `Tests/Multiselect` |
| 16 | Noise XX: ChaCha20-Poly1305 (RFC 8439 anchor), SymmetricState/CipherState, XX handshake (`Noise_XX_25519_ChaChaPoly_SHA256`), flynn/noise framework vectors + captured go-libp2p Transport transcript replay | `Conn/Noise`, `Tests/Noise` |
| 17 | TLS certificate extension: X.509 via OpenSSL backend, SignedKey DER decode, signature + peer-id derivation, all four tls.md vectors | `Conn/TlsExt`, `Tests/TlsExt` |
| 18 | yamux: 12-byte BE header codec (round-trip theorem), stream state machine, window accounting, ping echo, GoAway, byte-split e2e | `Conn/Yamux`, `Tests/Yamux` |
| 19 | mplex: header varint + length varint codec (round-trip theorem), seven flags, 1 MiB cap, byte-split e2e | `Conn/Mplex`, `Tests/Mplex` |
| 20 | Ping (`/ipfs/ping/1.0.0`, 32-byte echo) and Identify (`/ipfs/id/1.0.0`, protobuf, peer-id derivation) against a captured go-libp2p Identify response | `Protocol/Ping`, `Protocol/Identify`, `Tests/PingId` |
| 21 | signed envelopes (RFC 0002) + peer records (RFC 0003), verified against captured go-libp2p `record.Seal` output; `scripts/envelope-verify.go` for the reverse direction | `Crypto/Messages`, `Tests/Envelope` |

Open items from the phase 3 review — reconsidered during phase 4 and
still open (see "Real node" below):

- **mplex stream identity diverges from go-mplex**: go-mplex numbers each
  side's streams from zero and distinguishes them by the initiator bit;
  Lean keys streams by id alone with an odd/even split that go does not
  know, so ids from a go peer will collide with Lean's own.
- **yamux flow control is one-sided**: received WindowUpdate credit is
  recorded but never consulted on send, and accepted streams are never
  acknowledged (the opening WindowUpdate advertises a 256 KiB delta where
  go sends zero).
- **cacophony handshake hash**: the Noise framework vector carries a
  handshake hash that is extracted but not yet checked against the
  computed value (the pinned vector file ships empty `handshakeHash`
  fields, so a new capture is needed first).

To regenerate the go-libp2p wire captures:

```
docker run --rm -v $PWD/scripts:/src -w /src \
  -e GOFLAGS=-mod=mod golang:alpine \
  sh -c 'go mod init capture && go get github.com/libp2p/go-libp2p@v0.50.0 \
    github.com/flynn/noise@v1.1.0 github.com/multiformats/go-multistream@latest && \
    go build -o capture capture-vectors.go && \
    for m in mss noise identify envelope; do \
      ./capture -mode $m -o /src/out-$m.json; \
    done'
```
Then copy the `out-*.json` files into `Tests/vectors/` (with the
`_provenance` header from the committed copies).

Real go-libp2p wire captures in `Tests/vectors/`: `mss-go-trace.json`
(multistream full/na/lazy), `noise-go-transcript.json` (Noise XX
handshake + transport frames), `identify-go.json` (Identify protobuf),
`envelope-go.json` (PeerRecord envelope), `noise-vectors.json` (flynn/noise
Noise_XX_25519_ChaChaPoly_SHA256 vectors). The `scripts/capture-vectors.go`
tool produces all of these in a single `docker run` against go-libp2p
v0.50.0.

## Real node (phase 4)

Phase 4 (steps 22-24) turned the composition spike into a node:

| step | what | where |
|---|---|---|
| 22 | concurrency core: every polling loop replaced by promise-blocking primitives; `Chan` (closeable FIFO over `Std.CloseableChannel`), `TaskSet` (owned + joined tasks), mutex-guarded cells for the racy `IO.Ref` read-modify-writes; concurrent frame writes serialized per session; stream ids allocated atomically. Done: full suite passes under `+RTS -N1`, 1000-stream stress (950 sequential + 50 concurrent pings through one mux session) | `Conc`, `Conn/Mux`, `Conn/Yamux`, `Conn/Mplex`, `Sim`, `Tests/Node` |
| 23 | TCP transport over `Std.Internal.UV.TCP` (shipped in the v4.34 toolchain): `Tcp.dial`/`Tcp.listen` map `/ip4`/`/ip6` + `/tcp` addrs, reads are arbitrary prefixes, kernel segmentation is the hostile transport. Close semantics documented in the module (cancel paths drop promises, so `close` resolves the parked reader's promise itself and FINs the peer). Done: multistream (select/na/lazy/ls), Noise XX + transport, yamux and mplex through the upgrader — all over loopback TCP | `Net/Tcp`, `Tests/Tcp` |
| 24 | upgrader + host: security (`/noise`, ...) negotiated with multistream-select on the wire (sequential proposals, `na` retry, responder re-echoes a re-sent header); the muxer is picked from the Noise handshake extension with go-libp2p's exact selection rule (initiator orders by its own list, responder follows the initiator's order; empty intersection falls back to multistream-select - `Conn/Upgrade.matchMuxers`, mirroring vendor `p2p/net/upgrader.setupMuxer` + `p2p/security/noise.MatchMuxers`); `Session` bundles the verified remote `PeerId` with a uniform muxer handle; dial by PeerId through the peerstore or by a `/p2p/`-suffixed multiaddr (the suffix is the expected identity), verified after the handshake; per-peer connection dedup (races drop the loser); `Host.addrs` reports one `/p2p/`-encapsulated address per listener; `Host.close` joins every owned task. Done: two hosts ping/identify/echo over loopback TCP with real Ed25519 identities (`Tests/Node`), and **a Lean node pings a go-libp2p node and vice versa on loopback** (`scripts/ping-interop.sh`: go-libp2p v0.50.0 built in docker, `tcp + /noise + yamux`, extension-based muxer selection, both dial directions) | `Conn/Upgrade`, `Host`, `Main`, `PingNode`, `scripts/pingd.go`, `scripts/ping-interop.sh` |

The step 24 evidence is `scripts/ping-interop.sh`: it builds a go-libp2p
v0.50.0 node in docker, starts a Lean node (`pingnode`), and each side
dials the other and completes a `/ipfs/ping/1.0.0` round trip. The muxer
comes from the Noise extensions on both paths (the Lean dialer's
preference against go, go's preference against the Lean responder); no
multistream muxer negotiation happens, exactly like go. To re-run:
`bash scripts/ping-interop.sh`.

Notes from the implementation, worth keeping for the real implementation:

- **libuv cancellation drops promises.** `cancelRecv`/`cancelAccept`
  resolve nothing — a task parked on such a promise would hang forever.
  The TCP layer therefore never cancels: `close` resolves the parked
  promise itself (double resolve is a no-op in the task manager) and
  sends FIN, so the peer's readers see EOF and every task stays joinable.
  `send`/`recv?` themselves can also throw outright (dead handle); the
  wrapper turns that into read-EOF / dropped write.
- **Hand-off of buffered bytes between upgrade stages.** After a
  multistream negotiation completes, the responder starts the next stage
  (handshake, muxer) on the same connection; bytes that coalesced past
  the selection could sit in the negotiation reader and be lost. The
  dialer's round-trip discipline (it writes nothing past a proposal
  before reading the reply) closes this window for one proposal at a
  time; a real upgrader should thread one `BufReader` through all stages.
- **mplex EOF teardown.** The old spike's pump marked the session dead on
  EOF but left pipes/queues open — invisible while readers polled, a
  deadlock once reads block. Blocking primitives surface exactly this
  class of bug.
- **Per-chunk stream ciphers break on real transports.** The toy
  `noise-sim` XOR re-keyed at offset 0 for every read/write chunk; the
  sim preserves write boundaries so chunks always aligned, but TCP
  coalesces them (yamux header + payload!) and the keystream desynced
  into corrupted frames. It now tracks a byte position per direction -
  and every toy cipher must do the same.

Open items, recorded for phase 5 (surfacing against real peers):

- **mplex stream identity diverges from go-mplex** (go keys directions by
  the initiator flag and numbers both sides from zero; Lean uses an
  odd/even split), so mplex interop with go is not expected to work;
  yamux is the interop muxer. Related: yamux send-side flow control
  ignores received WindowUpdate credit and accepted streams are never
  acknowledged (fine for small transfers, wrong under load).
- **Simultaneous dials**: each side drops the newer inbound connection,
  so both can end up with nothing; needs go-style direction-based
  resolution.
- **TCP write errors are dropped** (a failed write surfaces later as
  read-EOF); a real node should propagate send failures to the stream.
- The cacophony handshake hash is extracted but not checked (the pinned
  vector file has empty `handshakeHash` fields; a new capture is needed).

## Interop (phase 5)

Phase 5 (steps 25-26, first matrix rows) turned the node into a
test-plan-shaped peer and paid the interop debt the wider matrix exposed:

| step | what | where |
|---|---|---|
| 25 | transport-interop harness: the `interop` exe reads `transport`, `muxer`, `security`, `is_dialer`, `ip`, `redis_addr`, `test_timeout_seconds`; the listener `RPUSH`es its multiaddr on the `listenerAddr` list, the dialer `BLPOP`s it, pings once and prints `{"handshakePlusOneRTTMillis": .., "pingRTTMilllis": ..}` (keys verbatim, typo included). A minimal RESP2 client (`LeanP2P/Interop/Redis.lean`) rides the TCP transport (DNS names resolve through a getaddrinfo shim); `scripts/interopd.go` is the go-libp2p counterpart reading the same env, and `interop/leanp2p/` (Dockerfile + Makefile emitting the upstream `image.json`) drops into a `libp2p/test-plans` fork as `impl/leanp2p/<v>/` | `Interop.lean`, `LeanP2P/Interop/Redis`, `scripts/interop-matrix.sh`, `interop/leanp2p/` |
| 26 | the recorded phase-4 blockers fixed to go semantics, then the live cells: **tcp × noise × yamux, lean ↔ go-libp2p v0.50, both dial directions, through Redis** (`scripts/interop-matrix.sh`, green; also wired into the nightly workflow, and verified once fully containerized: the leanp2p image as listener, a go container dialing it) | `Conn/Mplex`, `Conn/Yamux`, `Host`, `Net/Tcp`, `Tests/Interop` |

The interop debt fixed (all recorded as phase-5 blockers in phase 4):

- **mplex stream identity now matches go-mplex**: both sides number
  streams from zero and the Receiver/Initiator flag bit keys the stream
  (`id, weInitiated`) — simultaneous same-id streams coexist; the old
  odd/even split would collide with every go peer. In-process evidence:
  both sides open stream 0 at the same time and neither message crosses
  (`Tests/Interop`).
- **yamux honours the spec's flow control**: accepted streams are
  acknowledged (empty ACK window update — the spec requires ACK or RST),
  the initiator opens with an empty SYN window update (go-yamux
  semantics), sends are bounded by the peer-granted window (writers park
  on a credit channel; the session closes it on teardown), consumed
  bytes return as credit in half-window batches, and the credit ledger
  is exact (only application consumption returns credit). The frame
  pump never writes inline: pump-generated control frames (ACKs, ping
  echoes) go through a queue drained by a dedicated writer task, so a
  stream writer parked on a full TCP send buffer cannot stall the pumps
  of both sessions at once. Evidence: a 1 MiB round trip (4× the initial
  window) both directions over noise-encrypted TCP (`Tests/Interop`).
- **Simultaneous dials resolve go-style**: `Session.inbound` records who
  dialed; when an inbound/outbound pair *raced* (opposite directions
  within a freshness window), both sides keep the connection dialed by
  the peer with the smaller id, so the two decision points converge (the
  spike used to drop the newer connection, which could leave both sides
  with nothing). A later, non-racing connection never displaces a
  healthy session — go keeps both and only resolves genuine races — and
  a *dead* session is always replaced, so a restarted peer can
  reconnect (the decision re-runs the full rule when a concurrent decide
  changes the entry between probe and commit, sessions carry unique ids,
  and dead sessions are pruned from the reuse paths). The window is
  clock-local (documented divergence risk near its edge); the
  dead-replacement makes that self-healing. Known gap: a peer cannot
  replace a session we still consider live (no keepalive probe yet). Evidence: three rounds of
  concurrent dialing, one session survives on each side, pings work both
  ways; plus a killed-connection round trip where a fresh dial replaces
  the dead entry on both sides and pings again (`Tests/Interop`).
- **TCP write failures tear the connection down** (read EOF + FIN) so
  the mux/session layers observe them instead of losing bytes silently.
- **All yamux frame writes serialize on the session write mutex** — the
  frame pump started writing (ACKs), which raced handler writes at the
  Noise layer (two ChaChaPoly records with the same nonce). Post-review
  the pump no longer takes the mutex at all (control queue; above).
- Two latent bugs the stress exposed and fixed: `BufReader.readExactly`
  re-served buffered bytes (any leftover ≥ the request duplicated them
  into the stream — the noise/mux framing desynced), and the echo
  handler did not propagate EOF.

Two more pre-existing details worth keeping: mplex data for an unknown
stream is dropped (go-mplex logs and ignores), and go-libp2p v0.50
**removed mplex upstream**, so the mplex cells of the matrix are
reported as not-runnable-against-go; the Lean side's go-compatible
mplex is covered in-process.

Remaining phase 5 (recorded, not blocking): the `tcp × tls × yamux` and
`ws × noise × yamux` rows (needs the TLS 1.3 transport and a WebSocket
transport), the rust/js/nim columns (same harness, their test-plan
images), and steps 27-28 (QUIC/WebTransport/WebRTC through a backend;
hole-punch and perf suites). The nightly workflow runs the go cells.

## Architecture findings (the point of the spike)

**1. Structures beat typeclasses for the stack's interfaces.** `Transport`,
`SecurityProtocol`, `Muxer` are first-class structure values bundling
functions. libp2p picks implementations *dynamically* (per address, per
negotiation), and structure values compose/test/mock trivially
(`SimNet.transport`, `NoiseSim.security`, `FramedMux` are just values).
Typeclasses are reserved for genuinely static choices (`HashAlgorithm`).
Recommendation: keep this split.

**2. Pure verified cores + dumb IO shells work well.** Frame codec,
multiaddr binary form, and multiselect choice are pure functions with
proofs; the IO layers only plumb bytes. New codec => prove roundtrip once,
use everywhere. Recommendation: every protocol starts as a pure module with
a roundtrip/agreement theorem before any IO exists.

**3. Model wire bytes as `List Nat` in proofs, `ByteArray` only at the edge.**
`UInt8`/`ByteArray` arithmetic pulls in fixed-width-mod lemmas that fight
`simp`/`omega`; `List Nat` keeps everything in omega's domain. Conversions
live in one module (`Crypto/Bytes`). This is a spike-specific tradeoff to
revisit (BitVec would be the principled choice).

**4. Concurrency is the sharp edge (biggest lesson).**
- Lean's RTS defaults to **one capability**: background poll-loop tasks
  starve `main`. Phase 4 removed every poll loop (blocking channels +
  promises), and the whole suite now passes under `+RTS -N1`; run the
  demo with `+RTS -N8` or nothing at all.
- `IO.Ref` get-then-set is **not atomic** across tasks; phase 4 replaced
  the queues with `Std.CloseableChannel` and the counters/registries with
  mutex-guarded cells, so lost updates are gone.
- The RTS **waits for all tasks at exit** — phase 4 gives every task an
  owner (`TaskSet`, session task lists) and `Host.close` joins them; an
  abandoned promise (libuv cancel paths drop them) is the one way to hang
  a task forever, so the TCP layer resolves parked promises explicitly.
- Recommendation for the real implementation: keep the phase 4 shape —
  blocking FIFOs, owned tasks joined on close — and go further with a
  single-owner event loop per connection (no shared mutable queues at
  all).

**5. Composition pipeline proved out.** `dial -> security handshake ->
mux session -> openStream -> multiselect -> handler` layers with no
cross-layer leaks; adding a transport/protocol touches exactly one module.
Identify correctly derives the remote PeerId from the exchanged key through
the hash interface — the identity model is sound.

## Deliberate deviations from real libp2p

- End-to-end traffic is now encrypted and authenticated: the host
  negotiates `/noise` and runs the real Noise XX handshake (phase 3)
  over TCP (phase 4). Still toy: the `noise-sim` security (kept for the
  fast sim stress test) and the in-memory transport.
- Muxer selection matches go (Noise extension first, multistream
  fallback); the security protocol itself is negotiated with
  multistream-select one proposal at a time, like go's upgrader. The
  Noise handshake advertises exactly the host's muxer list, so the
  extension selection can only land on a muxer we actually have.
- Connection dedup keeps one session per remote PeerId; simultaneous
  dials resolve go-style (both sides keep the connection dialed by the
  peer with the smaller id, `Host.decide`).
- One transport (TCP), no keepalives, no relay/HolePunch/DHT. The
  remaining matrix rows (tls, ws, quic) and steps 27-28 are recorded in
  the phase 5 section.
- Frames assumed contiguous on read by the framed-sim muxer (the sim
  preserves message boundaries; TCP does not — the yamux/mplex readers
  handle arbitrary splits, and `Framing` decoding is only fed by the
  `buf` accumulator).
- mplex has no flow control (per spec); yamux implements the spec's
  window accounting (ACK on accept, send-side credit, half-window
  returns) but does not enforce the receive window on the peer.
- The harness advertises the configured `ip`; with the runner default
  `0.0.0.0` it falls back to the interface address its redis connection
  used, and `redis_addr` accepts DNS names (getaddrinfo in the C shim) —
  the compose-style `redis:6379` default works. Known gap: the dial/ping
  phase has no internal timeout (the runner's `test_timeout_seconds`
  provides for it).
