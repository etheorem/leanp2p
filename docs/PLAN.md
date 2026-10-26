# leanp2p: implementation plan

This plan is the companion to `docs/ARCHITECTURE.md`, and both live in
`docs/`. This file is authoritative for **order and dependencies**.
`ARCHITECTURE.md` stays authoritative for **contracts**.

## How to read this plan

- The plan cuts the work into units `W<wave>.<n>`. One person can
  implement and test each unit alone, against frozen interfaces.
- `deps:` lists the units that must reach their definition of done
  before this unit starts.
- **The first deliverable of every unit** is the `docs/ARCHITECTURE.md`
  and `docs/PLAN.md` of the target package (see ARCHITECTURE.md §2,
  "Per-package documentation"). Write them from the unit row below, the
  mechanisms of ARCHITECTURE.md §3, and the contracts of §4 and §5.
- **Definition of done**, the same for every unit:
  - the public surface follows ARCHITECTURE.md §4, shaped by the
    mechanisms of §3;
  - the owned contracts hold;
  - the carried vector and property tests pass;
  - the full suite passes under `+RTS -N1`;
  - the import-rule lint (ARCHITECTURE.md §2) is green.
- Priorities: **P0** is the consensus-critical path. **P1** is what
  consensus integration needs. **P2** is deferred, with seams only (see
  ARCHITECTURE.md §8).
- ARCHITECTURE.md §3 and §4 freeze the interfaces. The implementer of a
  unit can therefore write it against the frozen signatures before its
  dependencies finish. Only the test run waits for them. That lets the
  waves run in parallel.

## Dependency graph (tracks)

```
W0 scaffold
 ├── track A (codecs):      W1.2 → W2.1 → {W2.2, W2.3}
 ├── track B (crypto):      W1.2 → {W3.1, W3.2} → W3.3
 └── track C (net):         W1.1 (+W1.2) → W4.1 → {W4.2, W4.3}
W5 joins all three tracks (identity needs A+B, security needs B+C, mux/negotiate need C)
 └── W5.1 → W5.2 → {W5.3, W5.4} → W5.5 → W5.6 → W5.7 → W5.8 → W5.9
      (mplex, P2, can follow W5.4 at any time)
W6 consensus extension
 └── {W6.1 enr, W6.2 snappy} → W6.3 req/resp → W6.4 gossipsub
```

Three tracks run fully in parallel from W1 to W4. They join in the
libp2p wave (W5). The critical path is 15 units deep:
**W0 → W1.1 → W1.2 → W2.1 → W2.2 → W5.1 → W5.2 → W5.3 → W5.5 → W5.6 →
W5.7 → W5.8 → W5.9 → W6.3 → W6.4**.

## W0: repo scaffold (no dependencies)

Status: done. The three units are closed; `lake build` builds all 19
leaf libraries, the lint and the runner are green (also under
`+RTS -N1 -RTS`), and the vector corpus loads through its provenance
suite. CI runs on every push to `etheorem/leanp2p` and is green, the
vendor verify included.

| Unit | Deliverable | Done when |
|---|---|---|
| W0.1 | Lake skeleton: `packages/` tree with one `lean_lib` per leaf (§2), empty roots compile | `lake build` green with all leaves present |
| W0.2 | CI: import-rule lint (group chain §2, grep-enforced), test-runner layout (one suite module per upstream file, `lake test`, `-N1` required) | lint + empty runner green in CI |
| W0.3 | Vector infrastructure: `scripts/extract-vectors.py`, `VECTORS.lock`, `Tests/vectors/` moved from the `spike` branch | a trivial vector suite loads and passes |

## W1: foundations (parallel)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W1.1 | `base/conc` | P0 | W0 | `Chan` (every channel has a capacity) + `select` + task error surfacing, `Pipe`, `TaskSet`, `OnceRef`, `withinDeadline` over `select`, the `Clock` seam with a test value; wraps `Std.Sync`/`Std.Async` so that no other package imports them; contracts: never cancel, wake by close; owned tasks; atomic state |
| W1.2 | `base/bytes` | P0 | W0 | byte model ↔ `ByteArray`/`String`/hex; `Codec`/`LawfulCodec` classes and the shared `DecodeError` (ARCHITECTURE §3.2); the generic round-trip harness that all later codec units use |

## W2: codecs (parallel after W2.1)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W2.1 | `codec/varint` | P0 | W1.2 | encoder, decoder, and theorems; an over-long varint is a protocol error (`malformed`) |
| W2.2 | `codec/proto` | P0 | W1.2, W2.1 | `Fields`, encode/decode, last-wins singular lookups, round-trip theorem; the `ProtoMessage` class (ARCHITECTURE §3.2) |
| W2.3 | `codec/multiformats` | P0 | W1.2, W2.1 | multihash, multibase, base58, CID, multiaddr (full table, strict text parser, binary codec, operations API) |

## W3: crypto (parallel with W2)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W3.1 | `crypto/pure` | P0 | W1.2 | pure SHA-256/512, SHA-1, HMAC, HKDF with theorems |
| W3.2 | `crypto/backend` | P0 | W1.2 | own OpenSSL 3 bindings for what no etheorem package covers: Ed25519, X25519, RSA, SHA-1, SHA-512, HMAC, HKDF, ChaCha20-Poly1305, X.509, plus randomness and key generation; all `ByteArray` args **borrowed** (`@&`); pure bindings for deterministic primitives, `IO` for randomness (ARCHITECTURE §3.6); the etheorem hazmat integration: pins for `LeanHazmatSecp256k1`, `LeanHazmatP256`, `LeanHazmatSha256`, `LeanHazmatKeccak`, with the v4.34 build checks; verifier strictness (key type, RSA 2048–8192, low-S, validity + critical exts) |
| W3.3 | `Crypto` facade + cross-check | P0 | W3.1, W3.2 | the `Crypto` facade library (ARCHITECTURE §3.6; callers import only the facade) and the `Rng` seam; the pure package and the production path agree property-wise at the IO edge (RFC vectors both ways) |

## W4: networking (parallel after W4.1)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W4.1 | `net/streams` core | P0 | W1.1, W1.2 | `Connection`/`Listener`/`Transport`, `readExactly`, `BufReader`, `Framing`, `Stream` (+`prependBytes`) as the seam over a loop (ARCHITECTURE §3.3), the in-memory sim as the second `Transport` value |
| W4.2 | `net/streams` tcp | P0 | W4.1, W1.1 | libuv transport with the close-wakes discipline, failed-write teardown, deadline wiring for §5.4 |
| W4.3 | `net/yamux` | P0 | W4.1 | header codec (a proved `LawfulCodec`), session as a pure `step` + one loop task (ARCHITECTURE §3.3), flow control, hostile-frame rules (caps, SYN-only + parity, stream retirement, wake hand-off, capped control queue) |

## W5: libp2p (joins the tracks)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W5.1 | `libp2p/identity` | P0 | W2.2, W2.3, W3.3 | four key types, deterministic marshalings, strict unmarshal (per-type `Data` length), peer id (identity inlining ≤ 42 B), the key-marshal forms that the backend does not own |
| W5.2 | `libp2p/core` | P0 | W4.1, W5.1 | `ProtocolId`, `Core.Error`, the seam structures (`SecurityProtocol`/`SecureConn`, `Muxer`/`MuxSession`, `StreamHandler`, gater/resource-manager/address-ranker); types only, with no protocol logic (ARCHITECTURE §3.1, §4.9) |
| W5.3 | `libp2p/security` (Noise) | P0 | W4.2, W3.3, W5.2 | XX handshake as a pure `step` + transport; leftover hand-over as data; an AEAD failure is a protocol error, distinct from EOF; 8 KiB pre-auth payload cap; the `SecurityProtocol` value plus a fixed-key test value |
| W5.4 | `libp2p/mux` | P0 (mplex **P2**) | W4.3, W5.2 | the yamux `Muxer` value over W4.3; mplex later in the same package: go-compatible `(id, initiator)` identity, half-close rules |
| W5.5 | `libp2p/negotiate` | P0 | W5.2, W5.3, W5.4 | multistream-select as a pure `step` (1 KiB cap, `na`, `ls`, lazy) + upgrader over the `core` seams with leftover hand-over between stages |
| W5.6 | `libp2p/host` | P0 | W5.5, W5.1, W1.1 | host/swarm, per-peer dedup + simultaneous-dial rule as a pure table update, handler registry, peerstore, shutdown order (§5.5), `Host.Error`, policy seam values |
| W5.7 | `libp2p/protocols` | P0 | W5.6 | identify (+ push), ping |
| W5.8 | `cli/` | P0 | W5.7 | demo node + ping node binaries: the composition wiring, as running code that documents it |
| W5.9 | `cli/` interop | P0 | W5.8 | transport-interop harness; **gate**: go-libp2p matrix `tcp + /noise + yamux`, dial and listen, plus silent-peer and slow-reader scenarios |

## W6: consensus extension (P0/P1; see ARCHITECTURE.md §8)

| Unit | Pkg | P | deps | Deliverable |
|---|---|---|---|---|
| W6.1 | `libp2p/identity` ENR | P1 | W5.1, W3.2 | RLP from the etheorem monorepo (`etheorem/etheorem`, LGPL-3.0; the RLP package is upstream work not yet on its `main`, and unit 2 tracks it), wrapped behind the package's `Codec` surface, + ENR encode/decode + peer-id/multiaddr mapping (discv5 itself stays out of scope); the `v4` identity scheme verifies through the keccak-256 path of W3.2 (`LeanHazmatKeccak`), with ENR-local handling of the recovery-byte signature |
| W6.2 | `codec/snappy` | P0 | W1.2 | snappy FFI: the package binds upstream `google/snappy` (C++; the C++ runtime compiled out, the `LeanHazmatBn254` pattern) behind a Lean interface per the dependency strategy (FFI first; a native Lean replacement later, behind the same interface); block format only, raw `compress`/`decompress`, the length prefix stays in the req/resp framing (§8) |
| W6.3 | req/resp framework | P0 | W5.6, W6.2 | `/eth2/.../ssz_sn` framing: uvarint length + snappy, deadlines, error/EOF distinction; SSZ payloads stay client-side |
| W6.4 | gossipsub v1.1 | P0 | W5.6, W5.7, W1.1 (select/bounded queues) | RPC codec; mesh, scoring, and heartbeat as one pure `step` with time as an `Event` (ARCHITECTURE §3.3); signing policies; **gate**: gossipsub-interop against go and rust with no behavior difference |

## Deferred (P2: seams only, no scheduled work)

- TLS 1.3 and the X.509 extension (next to W5; the spike has a
  reference)
- mplex interop beyond W5.4
- QUIC and WebTransport transports (behind `Transport`)
- kad-dht, peer routing, rendezvous, fetch, mDNS
- relay and circuit, DCUtR, AUTONAT
- WebSockets, WebRTC, pnet, libp2p-HTTP
- peer records and signed envelopes

Each item must keep compiling against its seam. None may block a P0 or
P1 unit.

## Parallelism summary

- **After W0**: W1.1 ∥ W1.2 (two people).
- **After W1**: three tracks run at the same time. A is
  W2.1 → {W2.2, W2.3}, B is {W3.1, W3.2} → W3.3, and C is
  W4.1 → {W4.2, W4.3}.
- **After W5.2**: security (W5.3) and mux (W5.4) are independent.
  Identify and ping (W5.7), then `cli/` (W5.8), wait for the host only.
- **W6**: W6.1 ∥ W6.2 as soon as their deps finish. W6.3, then W6.4,
  end the critical path.
- Watch the contention points. `W2.1`, `W4.1`, `W5.2`, and `W5.6` each
  have three or more consumers, so put them first inside their waves.
