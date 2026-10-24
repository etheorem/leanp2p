# leanp2p — implementation plan

Companion to `docs/ARCHITECTURE.md`; the two live together in `docs/`. This file is authoritative for **order and
dependencies**; `ARCHITECTURE.md` remains authoritative for **contracts**.

## How to read this plan

- Work is cut into units `W<wave>.<n>`. Each unit is independently
  implementable and testable by one person against frozen interfaces.
- `deps:` lists the units that must reach their definition of done
  before this one starts.
- **Every unit's first deliverable** is the target package's
  `docs/ARCHITECTURE.md` + `docs/PLAN.md` (see ARCHITECTURE.md §2,
  "Per-package documentation"), written from the unit row below plus the
  contracts of ARCHITECTURE.md §3/§4.
- **Definition of done** (identical for every unit): public surface per
  ARCHITECTURE.md §3; the owned contracts hold; the carried vector and
  property tests pass; the full suite passes under `+RTS -N1`; the
  import-rule lint (ARCHITECTURE.md §2) is green.
- Priorities: **P0** = consensus-critical path, **P1** = needed for
  consensus integration, **P2** = deferred (seams only) — see
  ARCHITECTURE.md §7.
- Interfaces are frozen by ARCHITECTURE.md §3, so a unit may be
  *developed* against the frozen signatures before its dependencies
  finish; only running its tests waits for them. This is what makes the
  waves parallel rather than strictly sequential.

## Dependency graph (tracks)

```
W0 scaffold
 ├── track A (codecs):      W1.2 → W2.1 → {W2.2, W2.3}
 ├── track B (crypto):      W1.2 → {W3.1, W3.2} → W3.3
 └── track C (net):         W1.1 (+W1.2) → W4.1 → {W4.2, W4.3}
W5 joins all three tracks (identity needs A+B, security needs B+C, mux/negotiate need C)
 └── W5.1 → W5.2 → W5.4 → W5.5 → W5.6 → W5.7 → W5.8
      (W5.3 mplex hangs off W4.1 anywhere, P2)
W6 consensus extension
 └── {W6.1 enr, W6.2 snappy} → W6.3 req/resp → W6.4 gossipsub
```

Three tracks run fully in parallel between W1 and W4; the libp2p wave
(W5) is where they join. The critical path is
**W0 → W1.1 → W1.2 → W2.1 → W2.2 → W5.1 → W5.2 → W5.4 → W5.5 → W5.6 →
W5.7 → W5.8 → W6.3 → W6.4** (14 units deep).

## W0 — repo scaffold (no dependencies)

| Unit | Deliverable | Done when |
|---|---|---|
| W0.1 | Lake skeleton: `packages/` tree with one `lean_lib` per leaf (§2), empty roots compile | `lake build` green with all leaves present |
| W0.2 | CI: import-rule lint (group chain §2, grep-enforced), test-runner layout (one suite module per upstream file, `lake test`, `-N1` required) | lint + empty runner green in CI |
| W0.3 | Vector infrastructure: `scripts/extract-vectors.py`, `VECTORS.lock`, `Tests/vectors/` moved from the spike | a trivial vector suite loads and passes |

## W1 — foundations (parallel)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W1.1 | `base/conc` | P0 | W0 | `Chan` (incl. **bounded** variant + `select`/first-of + task error surfacing — beyond the spike), `Pipe`, `TaskSet`, `OnceRef`, `withinDeadline`; contracts: never cancel/wake by close, owned tasks, atomic state |
| W1.2 | `base/bytes` | P0 | W0 | byte model ↔ `ByteArray`/`String`/hex; fuzz-equivalence harness used by all later codec units |

## W2 — codecs (parallel after W2.1)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W2.1 | `codec/varint` | P0 | W1.2 | encoder/decoder + theorems; over-long = protocol error (never "need more bytes") |
| W2.2 | `codec/proto` | P0 | W1.2, W2.1 | `Fields`, encode/decode, last-wins singular lookups, round-trip theorem |
| W2.3 | `codec/multiformats` | P0 | W1.2, W2.1 | multihash, multibase, base58, CID, multiaddr (full table, strict text parser, binary codec, operations API) |

## W3 — crypto (parallel with W2)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W3.1 | `crypto/cores` | P0 | W1.2 | pure SHA-256/512, SHA-1, HMAC, HKDF with theorems |
| W3.2 | `crypto/backend` | P0 | W1.2 | OpenSSL 3 shim: Ed25519, X25519, secp256k1, ECDSA-P256, RSA, ChaCha20-Poly1305, X.509; all `ByteArray` args **borrowed** (`@&`); verifier strictness (key type, RSA 2048–8192, low-S, validity + critical exts) |
| W3.3 | crypto cross-check | P0 | W3.1, W3.2 | the cores and the backend agree property-wise at the IO edge (RFC vectors both ways) |

## W4 — networking (parallel after W4.1)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W4.1 | `net/streams` core | P0 | W1.1, W1.2 | `Connection`/`Listener`/`Transport`, `readExactly`, `BufReader`, `Framing`, `Stream` (+`prependBytes`), in-memory sim harness |
| W4.2 | `net/streams` tcp | P0 | W4.1, W1.1 | libuv transport with the close-wakes discipline, failed-write teardown, deadline wiring for §4.4 |
| W4.3 | `net/yamux` | P0 | W4.1 | header codec (proved), session, flow control, hostile-frame rules (caps, SYN-only + parity, stream retirement, wake hand-off, capped control queue) |

## W5 — libp2p (joins the tracks)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W5.1 | `libp2p/identity` | P0 | W2.2, W2.3, W3.3 | four key types, deterministic marshalings, strict unmarshal (per-type `Data` length), peer id (identity inlining ≤ 42 B), key-marshal forms the backend does not own |
| W5.2 | `libp2p/security` (Noise) | P0 | W4.2, W3.3, W5.1 | XX handshake + transport; reader threading; fatal-not-EOF AEAD failures; 8 KiB pre-auth payload cap; `SecurityProtocol` interface |
| W5.3 | `libp2p/mux` (mplex) | **P2** | W4.1 | interface + mplex, go-compatible `(id, initiator)` identity, half-close rules |
| W5.4 | `libp2p/negotiate` | P0 | W4.1, W5.2 (muxers: W4.3, W5.3) | multistream-select (1 KiB cap, `na`, `ls`, lazy) + upgrader with one-`BufReader` staging and leftover hand-off |
| W5.5 | `libp2p/host` | P0 | W5.4, W4.3, W5.1, W1.1 | host/swarm, per-peer dedup + simultaneous-dial rule, peerstore, shutdown order (§4.5), policy seams (gater/resource-manager interfaces) |
| W5.6 | `libp2p/protocols` | P0 | W5.5 | identify (+ push), ping |
| W5.7 | `cli/` | P0 | W5.6 | demo node + ping node binaries: composition wiring as executable documentation |
| W5.8 | `cli/` interop | P0 | W5.7 | transport-interop harness; **gate**: go-libp2p matrix `tcp + /noise + yamux`, dial and listen, plus silent-peer and slow-reader scenarios |

## W6 — consensus extension (P0/P1; see ARCHITECTURE.md §7)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W6.1 | `libp2p/identity` ENR | P1 | W5.1 | RLP codec (tiny, pure) + ENR encode/decode + peer-id/multiaddr mapping (discv5 itself stays out of scope) |
| W6.2 | snappy FFI | P0 | W1.2 | bind the C library behind a Lean interface per the dependency strategy (FFI first; native Lean replacement later behind the same interface) |
| W6.3 | req/resp framework | P0 | W5.5, W6.2 | `/eth2/.../ssz_sn` framing: uvarint length + snappy, deadlines, error/EOF distinction; SSZ payloads stay client-side |
| W6.4 | gossipsub v1.1 | P0 | W5.5, W5.6, W1.1 (select/bounded queues) | RPC codec, mesh, scoring, signing policies; **gate**: gossipsub-interop against go and rust with no behaviour difference |

## Explicitly deferred (P2 — seams only, no scheduled work)

TLS 1.3 + X.509 extension (W5-adjacent; spike reference exists), mplex
interoperations beyond W5.3, QUIC/WebTransport transports (behind
`Transport`), kad-dht, peer routing, rendezvous/fetch/mDNS, relay/circuit,
DCUtR/AUTONAT, WebSockets/WebRTC, pnet, libp2p-HTTP, peer records /
signed envelopes. Each must keep compiling against its seam; none may
block a P0/P1 unit.

## Parallelism summary

- **After W0**: W1.1 ∥ W1.2 (two people).
- **After W1**: three tracks run concurrently — A (W2.1→W2.2→W2.3),
  B (W3.1→W3.2→W3.3), C (W4.1→{W4.2, W4.3}).
- **After W5.1/W5.2**: security (W5.2) and mplex (W5.3, P2) are
  independent; identify/ping (W5.6) and `cli/` (W5.7) trail the host only.
- **W6**: W6.1 ∥ W6.2 immediately after their deps; W6.3 then W6.4 is the
  tail of the critical path.
- Contention points to watch: `W2.1` (three consumers), `W4.1` (four
  consumers), `W5.5` (four consumers). Prioritise them inside their waves.
