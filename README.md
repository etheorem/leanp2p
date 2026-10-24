# leanp2p

libp2p for Lean 4 — the implementation repository.

**Status: bootstrap.** This branch carries the architecture and the plan;
code lands package by package, bottom-up, in the order given in
[`docs/PLAN.md`](docs/PLAN.md). Nothing is implemented yet.

## What it is

A libp2p stack in Lean 4, targeting the **Ethereum consensus layer**
first: `tcp + /noise + /yamux`, identify, req/resp (`ssz_sn`) and
gossipsub v1.1. Everything else libp2p offers is a deferred seam behind
the interfaces (see ARCHITECTURE.md §7 for the full priority
classification).

Dependency strategy: where a mature implementation exists in another
language (OpenSSL today, snappy and QUIC stacks later), it is consumed
**FFI first** through a small C shim behind a Lean interface; a native
Lean implementation may replace it later behind the same interface.

## Layout

```
packages/
  base/     conc (concurrency primitives), bytes (byte model)
  codec/    varint, multiformats (multihash/multibase/base58/cid/multiaddr),
            proto (protobuf wire codec)
  crypto/   cores (pure, proved), backend (OpenSSL 3 via C shim)
  net/      streams (Connection/BufReader/Framing/tcp), yamux
  libp2p/   identity, security, mux, negotiate, host, protocols
  cli/      demo node, ping node, interop harness
```

Dependency rule: a group imports only groups to its right in
`cli → libp2p → net → crypto → codec → base`; everything left of
`libp2p/` never mentions libp2p and is usable by other projects.

## Documents

- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — package layout,
  per-package contracts, cross-cutting invariants, verification strategy,
  consensus-layer priorities. Authoritative for **what** and **why**.
- [`docs/PLAN.md`](docs/PLAN.md) — work units, dependency graph, build
  order. Authoritative for **order**; claim a unit there when
  implementing.
- `packages/<group>/<pkg>/docs/ARCHITECTURE.md` and `docs/PLAN.md` —
  written as the first work unit of every package; they refine the root
  documents and never contradict them.

## The reference implementation

The **`spike` branch** of this repository is a working libp2p spike:
wire formats proved and fuzz-pinned, captured go-libp2p vectors
(`VECTORS.lock`), a 3148-check suite, and a live go interop cell.
Consult it when implementing anything — its tests and vectors are the
source of the contracts — but it is a reference, not a spec: where
`docs/ARCHITECTURE.md` says otherwise, the architecture wins.

## Toolchain

Lean 4 (v4.34; see `lean-toolchain` on the spike branch) and OpenSSL 3
for `crypto/backend`. `lake test` runs the suite; the suite must pass
under `+RTS -N1` — that is the concurrency starvation criterion.
