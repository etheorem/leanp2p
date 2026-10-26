# leanp2p libp2p core: plan

This plan refines the root `docs/PLAN.md` for `libp2p/core`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). The package carries one implementation unit: unit 1 below is
the root unit W5.2, with deps W4.1 and W5.1. The done-when of unit 1
is the root row plus the root definition of done: the surface follows
ARCHITECTURE §4.9, shaped by §3, the owned contracts hold, the carried
tests pass, the suite passes under `+RTS -N1`, and the import lint is
green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W4.1, W5.1 | root W5.2: `ProtocolId`, `Core.Error`, `Role`, `SecurityProtocol`/`SecureConn`, `Muxer`/`MuxSession`, `StreamHandler`, and the three policy hooks; types only, with no protocol logic (§3.1, §4.9) | the root W5.2 row holds, and the unit 1 milestones below pass |

Unit 0 is done.

## Consumers

The surface freeze of this package is what lets the wave run. Root
PLAN: "After W5.2: security (W5.3) and mux (W5.4) are independent."
Root also names W5.2 a contention point with three or more consumers,
so it goes first inside its wave.

- `libp2p/security` (W5.3) fills `SecurityProtocol` with the Noise
  value and the fixed-key test value (§4.9).
- `libp2p/mux` (W5.4) fills `Muxer` with the yamux value over W4.3;
  mplex follows in the same package (P2, §8).
- `libp2p/negotiate` (W5.5) runs the upgrader over the core seams. It
  imports `core` and no implementation (§2, §3.1). The leftover
  hand-over between its stages travels in the `ByteArray` arguments
  and the `SecureConn` leftover (§4.7, §5.6).
- `libp2p/host` (W5.6) wraps `Core.Error` in `Host.Error` (§3.5),
  keys its registries by `PeerId` and `ProtocolId` (§3.8), and holds
  the `StreamHandler` registry of §3.10.
- `libp2p/protocols` (W5.7) registers its handlers by the
  `ProtocolId` constants of its own modules (§3.4).
- `cli/` (W5.8) assembles the ordered seam lists through these types
  and passes them to `Host.new` (§3.1).

## Test milestones (unit 1)

A types-only package closes its units at compile time. The suite
follows the root test-runner layout of W0.2, and each milestone below
is a check the build enforces.

- The seams admit their test values. A test module assembles a
  `SecurityProtocol` value from test doubles over the sim transport of
  `net/streams` (W4.1), a `Muxer` value over a toy session, and a
  `StreamHandler` over a toy callback. Each assembly is an `example`
  the build type-checks. When W5.3 and W5.4 land, their production
  and test values must compile against this frozen surface with no
  edit to `core`, or with a refinement `core` records first; their
  own plans carry that check. The spike already answered the
  openStream-hint question: `MuxHandle.openStream` takes the protocol
  name, mplex carries it in its NewStream frame, and the others
  ignore it (§10 row 12).
- The `Core.Error` arms construct and render. Each of the four arms
  builds from a rendered implementation error, and the rendered form
  reaches the log path (§3.5, §4.9).
- `Role` derives `DecidableEq`, `Repr`, and `Hashable` (§3.4). It has
  no `toCode`/`ofCode?` pair, because no spec gives roles a wire code
  (the architecture pair, public surface). If a code table appears,
  §3.4's total maps and the `ofCode?_toCode` theorem apply.
- `ProtocolId` carries its derived `DecidableEq` and `Hashable` (§3.4),
  and a registry-style lookup over it type-checks, the shape §3.10
  gives the host.
- The import lint: no module of this package imports
  `libp2p/security`, `libp2p/mux`, `libp2p/negotiate`,
  `libp2p/host`, or `libp2p/protocols` (§2). This package is the
  target the §2 lint guards for the rule "implementations import
  `core`; `negotiate` and `host` import `core` and no implementation".
- The `-N1` pass (§6, PRINCIPLES 5.3) is trivially green here: the
  suite is compile-level and spawns no task. The run stays in the
  definition of done, so the check exists even where it cannot fail.

## Vector stance

The package has no wire vectors and no behavior to pin. It touches no
wire bytes (§4.9: types only). The transcripts that exercise the
seams, the multistream traces, the Noise transport, and the yamux
frames, land with the implementation packages W5.3, W5.4, and W5.5
through W0.3 (§6). What this package pins is the surface those
implementations fill, and the compile milestones above close it.
