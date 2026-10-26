# leanp2p libp2p host: plan

This plan refines the root `docs/PLAN.md` for `libp2p/host`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Units 1a and 1b below are the root unit W5.6, with root deps
W5.5, W5.1, and W1.1. The done-when of unit 1b is the root row plus
the root definition of done: the surface follows ARCHITECTURE §4.9,
shaped by §3, the owned contracts hold, the carried tests pass, the
suite passes under `+RTS -N1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1a | W5.1, W5.2, W1.1 | the registries, the dedup rule, the peerstore, `Host.Error`, and the constants: pure functions over data, with their suites | the dedup, registry, and peerstore milestones below pass with no connection in the loop |
| 1b | 1a, W5.5 | the swarm: `dial`, `dialPeer`, `startListening`, the upgrade pipeline, stream serving, `Host.close`, and the policy values | the root W5.6 row holds, and the milestones below pass |

The split mirrors the negotiate pair's. Unit 1a is pure-function work
over the table types. It needs `PeerId` (W5.1), the seam types
(W5.2), and `OnceRef` (W1.1), and it closes with no connection in the
loop. W5.5 gates the seam calls and the end-to-end path of unit 1b,
so unit 1a lands while the upgrader finishes. W5.2 sits outside the
root row and reaches this unit through the root chain, which finishes
it before W5.5.

Unit 0 is done.

## Consumers

- `libp2p/protocols` (W5.7) registers identify and ping through the
  handler registry (§3.10). Root PLAN: identify and ping wait for the
  host only.
- `cli/` (W5.8) assembles the configuration: the ordered `Transport`,
  `SecurityProtocol`, and `Muxer` lists, the identity, the handlers,
  and the policy values, and passes them to `Host.new` (§3.1). It may
  override the permissive default gater.
- The interop matrix (W5.9) drives the host as the live gate: the
  go-libp2p matrix over `tcp + /noise + yamux`, dial and listen, plus
  the silent-peer and slow-reader scenarios (root PLAN W5.9).
  W6.3 and W6.4 build on the same surface: req/resp and gossipsub
  open streams and register handlers (root PLAN, W6 rows).

## Test milestones (unit 1a)

- Dedup, the pure function: a race between two opposite-direction
  dials of one peer inside the window keeps the connection dialed by
  the smaller id, tested in both directions, so the larger id's
  connection loses. A dial against a live standing session outside
  the window keeps the standing session. A dial when the standing
  session is dead, or absent, registers a new session.
- Concurrent dedup: two decisions over one peer each commit one
  survivor, per the rule, with no lost update. Under the
  single-update design there is no probe to race, and the test pins
  the atomicity PRINCIPLES 3.3 asks for. If a refinement
  reintroduces any probe, the retry path of PRINCIPLES 3.3 gets its
  own test.
- Liveness: a session loop that exits sets the table field through
  `OnceRef.update`, and the next dedup decision reads the entry as
  dead.
- Registries: the checks run as pure functions over the registry and
  its doubles, with no connection in the loop; the served-stream path
  is unit 1b's. A handler set under `OnceRef.update` is visible to a
  served stream. An unknown protocol answers `na`, and the stream
  closes. A handler failure closes the stream and reaches the owner
  through the task completion (the architecture pair, public surface).
- Peerstore: addresses round-trip. A redial's re-add of the same
  address leaves the set unchanged. N tasks add addresses to one
  store, and the store holds all of them, with no duplicates (the
  base/conc milestone shape, `OnceRef.update`).

## Test milestones (unit 1b)

- The upgrade pipeline over the sim, in both directions: dial and
  listen through the real `Noise.securityProtocol` value, or the
  fixed-key test value, and `Mux.yamux` (PRINCIPLES 1.4). An
  identity-check mismatch fails with the `Host.Error` arm that wraps
  `Core.Error.authentication` (§4.9; the negotiate pair).
- The silent-peer regression at host level (PRINCIPLES 5.4): a raw
  connection that sends nothing fails at the deadline, the
  pending-list close reaches the parked upgrade read, `close` joins
  every task, and the suite returns. The spike's test in
  `Tests/Node.lean` (a raw TCP client, a parked responder, one
  `close`) is the shape to carry. The test `Clock` of `base/conc`
  advances the deadline, so the suite waits on no wall clock.
- The shutdown order (§5.5): with ordering assertions or instruments,
  the stages run in sequence and every join returns, the closing
  flag, the listeners, the pending connections, the sessions, the
  session loops, the host tasks. A parked serve-loop accept wakes on
  the listener close.
- Leftover hand-over on a served stream (§4.7, §5.6): a byte the
  stream negotiation over-reads reaches the handler's first read, and
  nothing negotiated away is lost (the spike's prepend test,
  carried).
- The policy doubles: a denying gater blocks a dial with
  `Host.Error.gated`, and it refuses an accepted connection too (the
  core pair's gater answers for an outbound dial and for an inbound
  connection). The permissive gater passes both.
- The suite passes under `+RTS -N1` (§6, PRINCIPLES 5.3).

## Vector stance

No wire vectors concern the host. The host owns no codec: the
captured transcripts of §6 belong to the protocol packages, and the
upgrader's suites cover the negotiation bytes. The host's suites are
behavior tests over the sim transport, and the root W0.3
infrastructure serves them no fixtures. W5.9 is the live gate: the
go-libp2p matrix exercises the composed node against a foreign peer
and closes the unit for real.
