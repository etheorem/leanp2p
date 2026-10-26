# leanp2p

libp2p for Lean 4: the implementation repository.

**Status: bootstrap.** This branch carries the architecture and the
plan. Code arrives package by package, bottom-up, in the order of
[`docs/PLAN.md`](docs/PLAN.md). No package exists yet.

## What it is

A libp2p stack in Lean 4. Its first target is the **Ethereum consensus
layer**: `tcp + /noise + /yamux`, identify, req/resp (`ssz_sn`), and
gossipsub v1.1. Everything else that libp2p offers stays a deferred
seam behind the interfaces. ARCHITECTURE.md §8 gives the full priority
list.

Dependency strategy: **FFI first**. Some dependencies have a mature
implementation in another language: OpenSSL today, snappy and QUIC
stacks later. The stack binds each one through a small C shim behind a
Lean interface. A native Lean implementation may replace it later,
behind the same interface.

## Layout

```
packages/
  base/     conc (concurrency primitives), bytes (byte model)
  codec/    varint, multiformats (multihash/multibase/base58/cid/multiaddr),
            proto (protobuf wire codec)
  crypto/   Crypto facade; pure (pure-Lean digests, proved),
            backend (OpenSSL 3 via C shim); secp256k1, P-256, SHA-256,
            and keccak route to the etheorem hazmat packages
  net/      streams (Connection/BufReader/Framing/tcp), yamux
  libp2p/   identity, core (seam types), security, mux, negotiate, host, protocols
  cli/      demo node, ping node, interop harness
```

Dependency rule: in `cli → libp2p → net → crypto → codec → base`, a
group imports only the groups to its right. No package left of
`libp2p/` mentions libp2p, so other projects can use those packages.

## Documents

- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md): the package layout,
  how the parts connect (seams, classes, cores, loops), the contracts
  of each package, the cross-cutting invariants, the verification
  strategy, and the consensus-layer priorities. It is authoritative for
  **what** and **why**.
- [`docs/PLAN.md`](docs/PLAN.md): the work units, the dependency graph,
  and the build order. It is authoritative for **order**. Claim a unit
  there before you implement it.
- [`docs/PRINCIPLES.md`](docs/PRINCIPLES.md): the engineering
  discipline in detail. It explains what each rule means in practice,
  and which incidents led to it.
- `packages/<group>/<pkg>/docs/ARCHITECTURE.md` and `docs/PLAN.md`:
  every package writes these as its first work unit. They refine the
  root documents and never contradict them.
- [`CONTRIBUTING.md`](CONTRIBUTING.md): the pull request and issue
  workflow, the toolchain setup, and pointers to the code style.
- [`SECURITY.md`](SECURITY.md): the vulnerability disclosure policy.
- [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md): the community guidelines.

## The reference implementation

The **`spike` branch** of this repository holds a working libp2p spike.
Theorems prove its wire formats, and fuzz tests pin them. It holds the
captured go-libp2p vectors (`VECTORS.lock`), a 3148-check suite, and a
live go interop cell. Read it before you implement anything, because
its tests and vectors are the source of the contracts. Treat the spike
as a reference and `docs/ARCHITECTURE.md` as the spec. Where they
differ, the architecture wins. ARCHITECTURE.md §3 also fixes the code
shape.

## Toolchain

Lean 4 (v4.34; see `lean-toolchain` on the spike branch) and OpenSSL 3
for `crypto/backend`. `lake test` runs the suite. The suite must pass
under `+RTS -N1`, the criterion for concurrency starvation.

## License

LGPL-3.0-or-later; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
Every contribution falls under the contributor agreement in
[`CLA`](CLA).
