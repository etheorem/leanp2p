# leanp2p — architecture of the implementation

This is the blueprint for the **real implementation**, which starts from
scratch. The `spike` branch of this repository (phase 0-5; `VECTOR_TEST_PLAN.md` is
the record of how it was validated) is the **reference implementation**:
when implementing any piece, check the spike branch for the wire bytes, the
algorithm shape, the captured vectors and the regression tests - and for
the hardening rules, which are the distilled record of every bug the spike
and the review found. The spike is a reference, not a spec to follow
strictly: where this document says otherwise (bounded channels, the select
primitive, the package split), this document wins, and better local designs
are welcome as long as the contracts in §3 and §4 hold.

Everything below is stated as rules with a rationale, because those rules
are where the spike found its bugs - and the review found the rest.

---

## 1. Goal and non-goals

Goal: a libp2p node in Lean 4 that interoperates with go-libp2p on
`tcp + /noise + /yamux`, is safe against hostile peers on every
pre-authentication byte, shuts down deterministically, and keeps its
protocol cores machine-checked.

Non-goals (for v1): QUIC/WebTransport transports, kad-dht, pubsub, NAT
traversal, browser dialing. The layering below leaves room for all of
them; nothing else depends on their absence.

## 2. Package layout

The implementation starts from scratch as one repository with a
`packages/` tree. The tree has two levels: **groups** (things that belong
together: foundations, encodings, crypto, networking, the libp2p stack,
command-line executables) and, inside them, the packages themselves.

```
packages/
  base/                        foundations - no wire-format knowledge
    conc/                      Chan, Pipe, TaskSet, OnceRef, withinDeadline
    bytes/                     List-Nat byte model <-> ByteArray/String
  codec/                       encodings shared by everything above
    varint/                    unsigned varint (multiformats AND protobuf need it)
    multiformats/              multihash, multibase, base58, cid, multiaddr
    proto/                     protobuf wire codec
  crypto/
    cores/                     sha256/sha512/sha1/hmac/hkdf - pure Lean, proved
    backend/                   OpenSSL 3 C shim + @[extern] bindings
  net/                         connections and framing
    streams/                   Connection/Listener/Transport, BufReader,
                               Framing, Stream, tcp transport
    yamux/                     the stream muxer
  libp2p/                      the protocol stack
    identity/                  keys, peer ids
    security/                  SecurityProtocol, Noise XX, (tls ext: deferred)
    mux/                       muxer interface, mplex
    negotiate/                 multistream-select, upgrader
    host/                      swarm/host, peerstore, dedup, deadlines
    protocols/                 identify, ping, (echo demo)
  cli/                         command-line executables: demo node,
                               ping node, interop harness; config/wiring
```

Dependency rules, absolute and grep-enforceable in CI:

- **Between groups**: `cli → libp2p → net → crypto → codec → base` - a
  group only imports groups to its right.
- **Within groups, downward only**: `net.yamux → net.streams`,
  `codec.{proto,multiformats} → codec.varint`, `crypto.backend → base.bytes`.
- Everything left of `libp2p` must not mention libp2p; it is usable by
  other projects.

Varint gets its own package because two groups need it (the multiformats
spec and protobuf both frame lengths with it) and neither should own it.
`crypto.backend`'s *key marshaling* forms (SEC1/SPKI/PKCS#1 choices, the
key-type protobuf) belong to `libp2p.identity`, not to the backend - the
backend exposes only the primitive surface (§3.6).

One Lake package, one `lean_lib` per leaf. Splitting into separate
repositories is a later, mechanical move if external users appear; until
then version skew is a bigger risk than coupling.

**What `cli/` is for** (and is not): everything whose job ends at
`main` — executable entry points, CLI/config parsing, and the *wiring*
that turns the generic seams into a running node (which `Transport`, which
`SecurityProtocol` list, which muxers, which stream handlers). From the
spike that is `Main.lean`, `PingNode.lean`, and the interop harness exes.
Two rules keep it thin: `cli/` contains **no protocol logic and no
reusable code** (anything a second binary might want goes down into
`libp2p/` or lower), and `cli/` is **disposable** — a consumer project
(an Ethereum consensus client) brings its own node binary and uses only
the libraries; our `cli/` exists for the demo, the interop/test-plan
harnesses, and as executable documentation of how to compose the stack.

**Per-package documentation.** Documentation mirrors the tree. The
repository carries this file in `docs/` (cross-package contracts,
dependency rules, priorities) and `docs/PLAN.md` (implementation order and
parallel work units) beside it. Every leaf package carries its own two
documents:

- `packages/<group>/<pkg>/docs/ARCHITECTURE.md` — the package's internal
  design: module map, public surface, which §3/§4 contracts it owns and
  how it upholds them, decisions with rationale, and what it must not
  depend on;
- `packages/<group>/<pkg>/docs/PLAN.md` — the package's work units, their
  order, dependencies on other packages' units (by unit id, defined in
  the root `PLAN.md`), and the test/vector milestones that close them.

The hierarchy is strict: package docs refine the root docs and never
contradict them; a contract change starts at the root and flows down.
Writing the two package documents is the **first work unit of every
package** (see `PLAN.md`).

## 3. The packages

**Dependency strategy for external implementations.** Anything that
already exists as a mature implementation in another language (crypto
backends today; compression, TLS or QUIC stacks tomorrow) is consumed in
two phases: **FFI first, Lean later**. Phase 1 binds to the existing
library through a small C shim behind a Lean interface, exactly like
`crypto/backend` does with OpenSSL 3. Phase 2 - only where it pays -
re-implements it in pure Lean *behind the same interface*, as the spike's
SHA/HMAC/HKDF cores do: theorem-backed, and cross-checked against the FFI
at the IO edge. Interfaces are therefore designed for swappability from
day one: callers depend on the Lean interface, never on the FFI, so the
native implementation can land (or be rolled back to the FFI) without
touching call sites. For cryptographic primitives, constant-time code
stays in the C shim and the Lean version serves as the verified
cross-check; for non-cryptographic dependencies (e.g. snappy in §7) the
native replacement is the eventual goal, not just a check.

### 3.1 `base/conc` — concurrency primitives

`Chan` (closeable FIFO; close = broadcast EOF after drain), `Pipe` (byte
queue), `TaskSet` (owned tasks), `OnceRef` (atomic cell),
`withinDeadline` (bounded wait woken by close). Three rules, enforced
everywhere above it:

1. **Never cancel; wake by close.** The runtime drops cancelled promises;
   cancellation strands parked tasks. Every park must have a close that
   reaches it.
2. **Every task has an owner** that joins it. The RTS waits for tasks at
   exit; ownership is what makes exit possible.
3. **Shared state is atomic** (`OnceRef.update`), never get-then-set on a
   bare `IO.Ref`.

Additions over the spike, in priority order: a **bounded** `Chan`
(backpressure - the spike's unbounded queues were a review finding), a
**select/first-of** primitive (the deadline and the pump loops both hand-
rolled it), and **task error surfacing** (`joinAll` must not swallow
`Except IO.Error`).

### 3.2 `base/bytes` — the byte model

`List Nat` ↔ `ByteArray`/`String`/hex conversions. The `List Nat` model is
deliberate: arithmetic proofs (`omega`) stay tractable on it, and the
verified codec cores are stated over it. Every production path gets a
`ByteArray` decoder/encoder that is pinned to the model by fuzz property
tests (`decodeBinB b = decodeBin (toNatList b)`), so the proof-facing and
production views cannot drift.

### 3.3 `codec/varint` — unsigned varint

The LEB128 framing integer (multiformats spec): minimal encodings only,
at most 9 bytes (63 bits), with the round-trip and inverse theorems. A
varint that cannot complete within the byte budget is a **protocol
error**, never "need more bytes" - the reader-accumulates-forever bug is
banned here, at the source, so every consumer inherits it.

### 3.4 `codec/multiformats` — the spec family

Multihash (strict decode, function table), multibase (full registry),
base58btc, CID v0/v1, multiaddr (full protocols.csv table, strict text
parser, binary wire codec). This family carries its own conformance
suites (go + js vectors, fuzz corpora) - they travel with the library,
not with libp2p.

Rules validated in the spike, kept as requirements: text parsers are
strict (leading `/`, no empty segments, no `_` digit separators, no
leading-zero IPv4 octets); percent codecs operate on UTF-8 bytes, never
code points.

### 3.5 `codec/proto` — protobuf wire codec

Encode/decode over the byte model, framing lengths with `codec/varint`;
deterministic encoding (tag order, minimal varints) by construction;
unknown fields preserved; singular fields last-wins on decode.
Round-trip theorem on the core. libp2p messages (`Keys`, `Identify`,
`NoiseHandshakePayload`, `Envelope`, `PeerRecord`) live *above* this
package, in `libp2p`, as field tables.

### 3.6 `crypto` — the edge and the verified cores

Two packages under one group:

- **`crypto/cores`**: the pure Lean implementations (SHA-256/512, SHA-1,
  HMAC, HKDF): theorem-backed, used where auditability matters, always
  cross-checked at the IO edge against the backend.
- **`crypto/backend`**: the OpenSSL 3 shim (`c/p2pcrypto.c` + bindings):
  Ed25519, X25519, secp256k1, ECDSA P-256, RSA, ChaCha20-Poly1305, X.509.
  This is the "FFI first" phase of the dependency strategy (§3 preamble):
  the mature implementation is bound, not rewritten. Constant-time
  primitives are never written in Lean; the pure cores above are the
  "Lean later" phase, as verified cross-checks.

Rules from the spike, kept: every `ByteArray` argument to the shim is
**borrowed** (`@&`) - owned parameters leak one reference per call;
verifiers enforce **key type and size** (P-256 SPKI only; RSA 2048-8192
bits only; secp256k1 low-S only); X.509 validation checks validity time
and rejects unknown critical extensions. The libp2p key *marshalings*
(SEC1/PKCS#8/SPKI/PKCS#1 choices, key-type protobuf) belong to
`libp2p/identity`, not here; the EVP surface stays.

### 3.7 `net/streams` — connections and readers

`Connection` (read/write/close + addrs), `Listener`, `Transport`
(structure-valued, runtime dispatch - no typeclasses: muxers and
transports are chosen dynamically), `BufReader` (bytes over-read by one
framing layer stay available to the next), length-prefix `Framing`,
`Stream` (the application view over a muxer).

Two contracts live here and must not be lost:

- **TCP close discipline**: libuv drops cancelled promises, so `close`
  resolves the parked read's promise itself (double resolve is a no-op)
  and FINs the peer. A failed write tears the connection down (read EOF
  + FIN) instead of vanishing.
- **No reader strand**: whoever over-reads owns those bytes and hands
  them on. In the upgrader this means *one* `BufReader` threaded through
  every stage; at the application boundary it means prepending the
  negotiation reader's leftovers to the stream (`Stream.prependBytes`).

### 3.8 `net/yamux` — the interop muxer

The hashicorp spec over `net/streams.Connection`: 12-byte header codec
(proved round-trip), stream state machine, flow control. Hardened rules
from the spike, kept as requirements:

- Data frames are capped at the receive window we grant (256 KiB initial)
  **and** checked against it; over-window data is a protocol error, not a
  buffer.
- Only a **SYN frame with the remote's id parity** creates a stream;
  frames for unknown ids are dropped - they must never invent state that
  a later `openStream` could collide with.
- Streams are removed once both sides closed them; the session map must
  not grow monotonically.
- A writer that uses part of a credit grant hands the wake token on to
  the next parked writer.
- The control queue is capped (a hostile ping flood must not grow it).

### 3.9 `libp2p` — the protocol stack

Everything with libp2p semantics, in subpackages:

- **`identity/`** — Keys / PeerId (peer-ids spec): four key types,
  deterministic protobuf marshalings, identity inlining ≤ 42 bytes,
  strict unmarshal (key `Data` length validated per type - a 31-byte
  Ed25519 key must not derive an id). Also owns the key *marshalings*
  the crypto backend deliberately does not (§3.6).
- **`security/`** — Noise XX (`Noise_XX_25519_ChaChaPoly_SHA256`) and the
  TLS 1.3 extension scheme behind the `SecurityProtocol` interface
  (`Role → BufReader → IO (Option SecureConn)` - the handshake consumes
  the *same* buffered reader as the negotiation). Transport rules: a
  failed AEAD open is fatal (teardown), not EOF; handshake payloads are
  size-capped (8 KiB) before the pre-authentication decode; a failed seal
  tears the connection down. TLS ext is deferred (§7).
- **`negotiate/`** — multistream-select (1 KiB cap, `na` retry, `ls`,
  lazy dialer) and the upgrader.
- **`mux/`** — the muxer interface and mplex with go-compatible identity
  (both sides number from zero; streams keyed by `(id, initiator)`),
  already validated against the go behavior in the spike. Half-close per
  spec: close ends the closer's write direction only; reset is abortive
  both ways. yamux lives in `net/yamux` because it does not know libp2p.
- **`host/`** — upgrader pipeline security → identity-check → muxer;
  per-peer connection dedup with the simultaneous-dial rule (loser is the
  connection dialed by the larger id during the race window); peerstore.
- **`protocols/`** — identify (+ push), ping, req/resp and gossipsub when
  they land (§7).
- **Policy seams** (interfaces now, implementations later): connection
  gater, resource manager, address ranker.

## 4. Cross-cutting invariants

These are the invariants the implementation must preserve; each is
testable and most already have a regression test in the spike.

1. **Bounded receive path.** Every length-prefixed read is capped before
   allocation: framing lengths (multistream 1 KiB, mplex 1 MiB, yamux
   256 KiB, noise frame 64 KiB, noise payload 8 KiB pre-auth), flow
   control enforced on the sender, and over-long varints are protocol
   errors. The anonymous-connection cost of any single message is
   bounded by the cap, never by the attacker's length field.
2. **Verify before trust.** Anything decoded before the peer is
   authenticated is size-capped and, on failure, closes the connection;
   decode failures are distinguishable from EOF at every layer.
3. **Half-close semantics follow the muxer spec exactly** (mplex/yamux:
   close = write direction of the closer; the response after our FIN
   must still arrive).
4. **Unauthenticated phases are deadline-bounded** (`withinDeadline`;
   30 s like go): a silent dial or listener fails instead of parking a
   task forever. The deadline covers only the unauthenticated phase -
   authenticated-but-idle connections never expire.
5. **Deterministic shutdown.** Order: set closing flag → close listeners
   → close pending (unauthenticated) connections → shutdown sessions →
   join session pumps → join host tasks. Everything joins; nothing is
   parked without a close that reaches it.
6. **One reader per physical stream.** Negotiation, handshake, secure
   transport and muxer share a `BufReader` chain; stage handovers prepend
   leftovers rather than re-reading.

## 5. Verification strategy

Layered, matching how each part was validated in the spike:

1. **Theorems on pure cores** - varint/protobuf/framing/header codecs:
   round-trip and inverse properties over the byte model.
2. **Pinned upstream vectors** (`VECTORS.lock`, `scripts/extract-vectors.py`):
   RFC test vectors, go-libp2p fixtures, multiformats CSVs, captured
   transcripts (multistream traces, noise transport, identify, envelopes).
3. **Fuzz property tests** for the `ByteArray` production paths (the
   decoder actually on the wire must equal the proved model).
4. **In-process e2e**: hostile-transport sim (byte-splitting, sim net) and
   loopback TCP - every hardening rule above has a regression test.
5. **Interop matrix** against go-libp2p (dial/listen × muxers) plus the
   silent-peer and slow-reader scenarios.

The suite must keep passing under `+RTS -N1` - that is the starvation
criterion the concurrency rules buy.

## 6. Bootstrapping: the way to start

The implementation starts from scratch, bottom-up: write each package of
§2 in dependency order, and treat the **spike branch as the working
reference** while doing it. "Reference" means: for every package there is
spike code that produces spec-correct wire bytes, a captured vector suite,
and a regression-test list distilled from real bugs - consult it before
implementing, port its *tests* (they encode the contracts), and reuse its
theorem statements. It does not mean copying files blindly or matching its
internal structure: the package split differs (§2), and where this
document mandates a change (bounded `Chan`, select/first-of, deadline
coverage) the spike is deliberately *not* to be followed. When the spike
and this document agree, following the spike's shape saves you from
re-finding its bugs.

Build order (each step is `packages/<group>/<pkg>`):

| # | Package | Reference (spike files) | Public surface | Tests to carry over | Notes |
|---|---|---|---|---|---|
| 1 | `base/conc` | `Conc.lean` | `Chan` (new/send/recv/close/drain), `Pipe`, `TaskSet` (new/spawn/joinAll), `OnceRef` (new/get/set/update), `withinDeadline` | contracts: FIFO, close = broadcast EOF after drain, idempotent close, parked-recv wake, joinAll waits, N×M atomic updates, deadline wakes parked work via the close hook | implement bounded `Chan` + select/first-of + task error surfacing *here*, not later (§7's queues want them) |
| 2 | `base/bytes` | `Crypto/Bytes.lean` | `Bytes.{ofNatList,toNatList,ofString,toString?,ofHex?,toHex,xorWith,...}` | byte-model round-trips, fuzz equivalence (from the multiaddr/proto suites) | the proof-facing `List Nat` model is the point; document why |
| 3 | `codec/varint` | `Net/Varint.lean` | `encode(B)`, `decode?`, `decodeB?` + theorems | RFC examples, non-minimal/too-long rejection tests | over-long varint = protocol error, here at the source |
| 4 | `codec/proto` | `Crypto/Pb.lean` | `Fields`, `encodeFields(B)`, `decodeFields(B?)`, `get{Varint,Bytes,Sub,Str}?` (last-wins), `getAll*`, `hasField` | round-trip theorem, message-vector suite (field tables stay in libp2p) | deterministic encoding by construction |
| 5 | `codec/multiformats` | `Crypto/{Multihash,Multibase,Base58,Cid}.lean`, `Net/Multiaddr.lean` | as named, plus `Multiaddr.parse?/toString/toByteArray/ofByteArray?`, operations API | RFC/multiformats vector suites + go/js CSVs + fuzz corpora + proved round-trips | strictness rules travel (leading `/`, no empty segments, percent = UTF-8 bytes) |
| 6 | `crypto/cores` | `Crypto/{Sha256,Sha512,Sha1,Hmac,Hkdf}.lean` | digests, HMAC, HKDF | RFC vector suites + OpenSSL cross-checks | cross-checked against the backend at the IO edge |
| 7 | `crypto/backend` | `Crypto/OpenSsl.lean`, `c/p2pcrypto.c` | Ed25519/X25519/secp256k1/ECDSA-P256/RSA sign+verify, ChaCha20-Poly1305 seal/open, X.509 helpers; every `ByteArray` argument **borrowed** (`@&`) | fixture suites + verifier-strictness regressions (key type, RSA 2048-8192, low-S, X.509 validity + critical exts) | key *marshalings* are NOT here - they go to `libp2p/identity` (§3.6) |
| 8 | `net/streams` | `Net/{Transport,Tcp}.lean`, `Conn/{Reader,Frame,Stream}.lean`, `Sim.lean` | `Connection`/`Listener`/`Transport`, `readExactly`, `BufReader`, `Framing`, `Stream` (+`prependBytes`), sim harness | TCP suite (dial/listen, mss over TCP, noise over TCP, muxers over TCP), silent-peer teardown | contracts: libuv close-wakes discipline; failed write = teardown; no reader strand (one `BufReader` through every stage, leftovers prepended at the app boundary) |
| 9 | `net/yamux` | `Conn/Yamux.lean` | header codec, session, muxer entry | yamux suite + hostile-frame regressions + interop prereqs | keyed only by `net/streams.Connection`; caps, window enforcement, SYN-only creation, stream retirement, wake hand-off travel as contracts |
| 10 | `libp2p/*` | everything else in the spike (`Host.lean`, `Conn/{Upgrade,Security,Noise,TlsExt,Mplex}.lean`, `Crypto/{Keys,PeerId,Messages}.lean`, `Protocol/*`, `Peer/*`) | see §3.9 | node suite + noise suite + keys suite + interop prereqs | build order inside: identity → security/noise → negotiate → host → protocols; mplex last (deferred for consensus, §7) |
| 11 | `cli/` | `Main.lean`, `PingNode.lean`, `Interop.lean`, `scripts/` | node binaries + harness | e2e demo + interop matrix | also move `VECTORS.lock` + `scripts/extract-vectors.py` + `Tests/vectors/` here - they are implementation-independent |

Definition of done per package: the contracts of §3 hold, the carried-over
vector suites pass, and the dependency lint (no imports above the group
chain of §2) is green. The spike's test runner layout (one suite module
per upstream file, `lake test`, `-N1` pass required) is worth copying
wholesale.

## 7. Component priority: Ethereum consensus layer

The implementation targets a beacon-node (consensus-layer) client first.
This classification decides build order; "defer" means the interface
seams must exist but no implementation work is scheduled.

**Required by consensus (build in this order):**

| Component | Why | Status in spike |
|---|---|---|
| TCP transport | consensus networking runs on TCP (and QUIC) | done |
| Noise XX (`/noise`) | the only security protocol in the eth2 networking spec | done |
| yamux | required muxer over TCP (mplex removed from the spec; QUIC muxes internally) | done, hardened |
| multistream-select | negotiation for security + muxer | done |
| multiformats (multiaddr/varint/peer-id multihash, base58/base32) | dialing, ENR ↔ multiaddr, peer ids | done |
| keys + peer id, **Ed25519** (+ secp256k1 host keys) | host identity; clients use Ed25519/secp256k1 | done (Ed25519 fully; secp256k1 done too) |
| identify (+ identify-push) | peer metadata; gossipsub peer scoring | done (push trivial) |
| protobuf codec + key/identify messages | identify, ENR, host keys | done |
| **req/resp framework** (`/eth2/.../ssz_sn`) | Status, BlocksByRange/ByRoot, BlobSidecarsByRange/ByRoot, Metadata, Ping, Goodbye - SSZ + **snappy** framing over libp2p streams | **new work** (snappy is a new dependency: FFI to the C library first - §3 dependency strategy; SSZ encoding is pure Lean) |
| **gossipsub v1.1** | blocks, aggregates, slashings, exits, blob sidecars | **new work** (the largest component) |
| host/upgrade/peerstore, dedup, deadlines | everything above composes through them | done (TTLs/limits deferred) |
| ENR ↔ multiaddr/peer-id mapping | discovery integration (discv5 itself is *not* libp2p - out of scope here) | multiaddr side done; ENR codec new (simple: RLP) |

**Optional / opportunistic (spec-legal but not required):**

- QUIC transport (widely enabled by clients; natural second transport) -
  webtransport after it if ever.
- libp2p `/ipfs/ping/1.0.0` as keepalive (cheap; some clients use it -
  consensus keepalive itself is the eth2 req/resp Ping).
- CIDv1 (`bafz...`) peer-id text form (compat nicety; already built).
- Hole punching (DCUtR/AUTONAT), circuit relay - some clients
  experimentally support them; consensus works without.

**Not needed for consensus (defer, keep seams only):**

- **TLS 1.3 security + X.509 libp2p extension** - not in the eth2 spec
  (Noise only); spike work is done, no further investment.
- **mplex** - removed from the eth2 networking spec.
- **RSA and ECDSA P-256 host keys** - consensus clients use
  Ed25519/secp256k1; RSA especially is a go-libp2p default, not an eth2
  one.
- **Peer records / signed envelopes (RFC 0002/0003)** - unused by
  consensus; spike work done, defer.
- **kad-dht, peer routing, content routing** - consensus has no DHT.
- **rendezvous, fetch, mDNS** - discovery is discv5's job.
- **WebSockets, WebRTC, pnet (private networks), libp2p-HTTP** - absent
  from consensus networking.
- Unix/memory multiaddr transports - already part of the multiformats
  table; no libp2p-side work.

Practical consequence for ordering: the post-spike critical path is
**req/resp + snappy → gossipsub v1.1 → ENR codec**, plus the `conc`
additions (bounded channels, select) that gossipsub's queues will want.
Everything in the "not needed" list stays a seam in the interfaces that
already exist (`SecurityProtocol`, `MuxChoice`, `Transport`, policy
hooks) - deferred, not designed out.

## 8. Deltas: spike → implementation

Known gaps the spike records and the implementation must close:

1. Bounded channels / backpressure in `base/conc` (§6, step 1 - do it there,
   not as a later delta).
2. Keepalive / identity probe so dead sessions are noticed without
   waiting for a write failure or TCP EOF (dedup currently needs this to
   retire sessions promptly).
3. Peerstore limits and TTLs; address dedup already done.
4. Connection gater + resource manager seams filled (limits per peer /
   per connection: stream count, buffered bytes, memory ceiling).
5. Select/first-of primitive replacing the polling deadline internally
   (observable behavior unchanged).
6. QUIC transport - second priority after the consensus-critical
   protocols, before anything else in §7's optional list.
7. Build out `Streams` if a second transport lands - the libuv binding is
   toolchain-internal (`Std.Internal.UV`, v4.34) and must stay swappable.

## 9. Reference map (spike module → package)

Where each spike module's content lands in the `packages/` tree (§2).

| Spike module | Package |
|---|---|
| `Conc.lean` | `base/conc` |
| `Crypto/Bytes.lean` | `base/bytes` |
| `Net/Varint.lean` | `codec/varint` |
| `Crypto/{Multihash,Multibase,Base58,Cid}.lean`, `Net/Multiaddr.lean` | `codec/multiformats` |
| `Crypto/Pb.lean` | `codec/proto` |
| `Crypto/{Sha256,Sha512,Sha1,Hmac,Hkdf}.lean` | `crypto/cores` |
| `Crypto/OpenSsl.lean`, `c/p2pcrypto.c` | `crypto/backend` (key forms → `libp2p/identity`) |
| `Net/{Transport,Tcp}.lean`, `Conn/{Reader,Frame,Stream}.lean` | `net/streams` |
| `Sim.lean` | `net/streams` test-support (in-memory transport) |
| `Conn/Yamux.lean` | `net/yamux` |
| `Crypto/{Keys,PeerId}.lean` | `libp2p/identity` |
| `Conn/Security.lean`, `Conn/Noise.lean`, `Conn/TlsExt.lean` | `libp2p/security` (TlsExt deferred, §7) |
| `Protocol/Multiselect.lean`, `Conn/Upgrade.lean` | `libp2p/negotiate` |
| `Conn/Mplex.lean` | `libp2p/mux` |
| `Host.lean`, `Peer/Peerstore.lean` | `libp2p/host` |
| `Protocol/{Identify,Ping}.lean`, `Crypto/Messages.lean` | `libp2p/protocols` (Messages' envelope/record tables deferred, §7) |
| `Main.lean`, `PingNode.lean`, `Interop.lean` | `cli/` |
