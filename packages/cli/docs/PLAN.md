# leanp2p cli: plan

This plan refines the root `docs/PLAN.md` for `cli/`. The package
carries two root units: W5.8 (the demo and ping binaries) and W5.9
(the interop harness and its gate). The done-when of each is the root
row plus the root definition of done: the surface follows ARCHITECTURE
§2, the owned contracts hold, the carried tests pass, and the import
lint is green. The `+RTS -N1` pass covers the in-suite parts; the
W5.9 gate runs live, outside the suite runner.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W5.7 | the demo node and the ping node binaries, with the composition wiring, as running code that documents it (root W5.8) | the root W5.8 row holds, and the unit 1 milestones pass |
| 2 | 1 | the transport-interop harness, closed by its gate: the go-libp2p matrix `tcp + /noise + yamux`, dial and listen, plus the silent-peer and slow-reader scenarios (root W5.9) | the gate passes, and the unit 2 milestones pass |

Unit 0 is done.

Unit 1 has the executable composition, parser and workflow tests.
It is ahead of its dependencies under RULES.md. The mock-backed build
is reviewable; unit 1 remains open until the mocks are replaced and
the real loopback and bidirectional Go ping gates pass.

The opaque mock bodies fail at program entry. A passing `Tests.Cli`
run is an orchestration result, not evidence of a Noise handshake,
yamux negotiation, identity derivation or a live ping.

Build and inspect the commands with:

```sh
lake build demo pingnode
./.lake/build/bin/demo --help
./.lake/build/bin/pingnode --help
lake test
lake test -- +RTS -N1 -RTS
python3 -m unittest discover -s scripts -p test_ping_interop.py
```

The two live gates are explicit skips while the dependencies are
mocked. After substitution, run the demo over loopback and run
`scripts/ping-interop.sh` on Linux with Docker available. The Go helper
uses the committed `scripts/ping-peer/go.mod` and `go.sum`, with
read-only module resolution.

The dependency connections are:

- W2.3: replace the address type, parser, printer and component view
  with the canonical `Multiformats.Multiaddr` API.
- W3.3 and W5.1: generate fresh Ed25519 identities and Noise static
  keys through the real crypto and identity APIs. Replace the mock
  peer-id display. Keep randomness errors fatal; there is no fallback.
- W4.2, W5.3 and W5.4: replace TCP, Noise and yamux seam values.
  Muxer negotiation stays on the wire, with no advertised Noise muxer
  extension and no implicit mplex choice.
- W5.6: adapt the CLI-side host view to the concrete configuration,
  binding, peerstore, stream-opening and close/join API. Confirm that
  `startListening` exposes the actual bound address for port zero.
- W5.7: replace ping and identify adapters and the demo echo support
  with their protocol implementations. The binaries match only on
  `Host.Error` after this mapping.

Drop these mocks within the RULES.md window after the dependencies
merge. Rerun the build, both scheduler modes, the import lint, the
workflow checks and both live gates. This PR must not merge while its
dependency mocks remain. Update tracking issue #25 when the real
connections are complete.

## Consumers

None below. `cli/` is the end of the chain (§2), and nothing imports
it. The consensus client of §8 is the external consumer: it brings its
own node binary and uses only the libraries. The harness serves the
verification plan (§6, layer 6). The W6.4 gate is a later consumer of
the same pattern, a live run against foreign nodes.

## Test milestones (unit 1)

`Tests.Cli` checks strict argument arity, decimal port boundaries,
help without host creation, parsed peer suffixes, exact readiness and
ping output, stdout flushing, stream cleanup, both host lifetimes,
and injected IO faults. These checks run in `lake test` and under
`+RTS -N1`.

`scripts/ping-interop.sh` runs the live gate through the bounded Python
driver. It requires Linux because Docker builds a Linux Go peer that
runs beside Lean on the host. The driver starts Lean before building
Go, so an unavailable dependency fails before Docker is invoked. It
uses ephemeral ports, checks readiness, bounds child lifetimes, closes
stdin and joins both servers. It reports success only after both
dial directions pass and both servers exit cleanly.

The current validation passes 123 orchestration checks inside the
full suite, plus eight Python driver checks. The Go helper compiles
with CGO disabled for macOS and Linux using read-only module
resolution. The two live gates remain unrun and are explicit skips;
successful helper compilation does not close either gate.

- The demo runs end to end over loopback: two hosts dial, complete the
  upgrade, identify, and exchange pings and an echo. The spike's
  node-suite legs are the carried tests (the spike's `Tests/Node.lean`
  drives two hosts over loopback TCP through ping, identify, and
  echo).
- Ping interop with go (the spike's `ping-interop.sh` shape): the
  script builds `pingd.go` in docker (go-libp2p v0.50.0, CGO off),
  starts both nodes on loopback, and dials in both directions over
  `tcp + /noise + yamux`: lean dials go, and go dials lean. The
  spike selected the muxer from the Noise handshake extension. The
  target advertises no muxers there, so both sides negotiate the
  muxer on the wire (the negotiate pair's decision).
- The in-suite legs pass under `+RTS -N1` (§6; PRINCIPLES 5.3).

## Test milestones (unit 2)

- The gate: the interop matrix against go-libp2p v0.50.0, over
  `tcp + /noise + yamux`, dial and listen, both directions, with the
  two harness executables coordinated through Redis in docker, per
  `scripts/interop-matrix.sh`. A cell passes when the dialer prints
  the timing JSON of the `interop` contract.
- The matrix cells for mplex are skipped against go v0.50, which
  removed mplex upstream (the mux pair's record). The Lean side's
  mplex identity stays covered in-process, as the spike's
  `Tests/Interop.lean` does.
- The silent-peer scenario, the carried regression (PRINCIPLES 5.4):
  a raw connection that sends nothing fails the upgrade at the
  deadline (§5.4), and teardown closes the pending connection and
  joins every task. The host pair carries the in-suite form; the gate
  runs it live against the composed binary.
- The slow-reader scenario: the spike ran no live leg for it. The
  in-process evidence is the yamux flow-control work, a transfer
  larger than the 256 KiB initial window completing in both directions
  over noise-encrypted TCP, and data beyond the receive window failing
  as a protocol error. Unit 2 designs the live scenario against §5.1's
  bounded receive path and records its shape here when it lands.
- The `-N1` statement: every in-suite test of both units passes under
  `+RTS -N1` (§6; PRINCIPLES 5.3). The gate runs foreign processes
  under docker, outside `lake test`, and the scripts carry their own
  bounds, `test_timeout_seconds` among them.

## Vector stance

The harness adds no vectors, and the package consumes none. The
carried node-suite legs are behavior tests over loopback with no
fixtures, as the spike's `Tests/Node.lean` records. The fixture
suites of ping and identify belong to the protocol packages. The gate
is a live run against go-libp2p, and no vector file covers it,
because a foreign peer's live behavior is the thing under test. Its
result lands in the unit 2 close-out note of this plan.
