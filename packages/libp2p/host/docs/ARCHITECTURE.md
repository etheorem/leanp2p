# leanp2p libp2p host: architecture

`libp2p/host` composes the stack into a node. It holds the ordered
transport, security, and muxer lists as configuration (§3.1), runs the
upgrade pipeline of §4.9 per connection, keeps the three registries of
§3.8 (the live sessions by peer, the stream handlers by protocol id,
and the peerstore), serves inbound streams through the handler
registry (§3.10), and owns the shutdown order of §5.5. It is the last
stop in the libp2p chain before `libp2p/protocols` (§2). The spike
reference is `Host.lean` and `Peer/Peerstore.lean` (§10, row 16; the
libp2p group is §7, row 10).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Host.lean` | the root module; one import line per public submodule |
| `Libp2p/Host/Constants.lean` | the simultaneous-dial window and the host-owned timeouts; one home per fact (§3.8) |
| `Libp2p/Host/Error.lean` | `Host.Error`, the error the host and `cli/` match on (§3.5) |
| `Libp2p/Host/Registry.lean` | the session and handler registries, each a `Std.HashMap` inside an `OnceRef`, their pure update functions, and the shared table types (§3.8, §3.10) |
| `Libp2p/Host/Dedup.lean` | the dedup rule as one pure function over the session table |
| `Libp2p/Host/Peerstore.lean` | the third registry, addresses by peer, deduplicated at add (§3.8) |
| `Libp2p/Host/Swarm.lean` | `dial`, `dialPeer`, `startListening`, the accept loop, the upgrade pipeline, and stream serving |
| `Libp2p/Host/Shutdown.lean` | `Host.close`, the §5.5 sequence |
| `Libp2p/Host/Policy.lean` | the permissive default gater, and the permissive and denying test doubles the core pair assigned here |

All declarations live in the `Libp2p.Host` namespace, and the root
module re-exports the public submodules.

## Public surface

- `Host.new` takes the configuration: the ordered `Transport`,
  `SecurityProtocol`, and `Muxer` lists (§3.1), the host identity as a
  private key from `libp2p/identity`, the initial handler set, and the
  policy values. The lists are parameters, and no host module names a
  concrete seam value.
- `dial` dials one address or reuses a live session. A trailing
  `/p2p/<id>` component supplies the expected `PeerId` when the
  argument gives none (the spike's rule, kept). `dialPeer` takes the
  addresses from the peerstore and walks them. The dedup race window
  sits at the commit, per contract 2 below.
- The listen side: `startListening` binds one address, registers the
  listener, and spawns the accept loop. Each accepted connection
  enters the upgrade pipeline as a pending connection.
- `setHandler` stores one `StreamHandler` under its `ProtocolId`
  through `OnceRef.update`. The registry is the
  `Std.HashMap ProtocolId StreamHandler` of §3.10. A handler failure
  closes the stream, never the session, and the error reaches the
  owner through the spawned task's completion (PRINCIPLES 3.2). This
  settles the question the core pair left open.
- The peerstore surface: `addAddrs` (deduplicated at add, so a redial
  grows nothing) and `addrsOf`. Limits and TTLs stay deferred (§9,
  delta 3).
- `Host.Error` wraps `Core.Error` and adds arms of its own (§3.5).
  The proposed arms: `upgrade Core.Error`, the coarse pipeline error
  with the rendered inner error for the log; `gated`, a policy hook
  denied the dial or the inbound connection; `noAddresses PeerId`,
  `dialPeer` found no peerstore addresses; `closing`, the host is shut
  down or shutting down. The set covers what the spike's paths can
  fail with, and the package refines it at implementation time.
- `close` runs the shutdown sequence of §5.5.
- The policy values: `Policy.permissiveGater` is the default gater,
  and it allows everything. The permissive and denying gaters are the
  test doubles. The limiting implementations of §9, delta 4, land
  later behind the same seam.

## Owned contracts and how the package keeps them

1. **Every registry changes only under `OnceRef.update`, through a
   pure update function** (§3.8, PRINCIPLES 3.3). No get-then-set on a
   bare `IO.Ref` appears anywhere in the package. The update functions
   are data in, data out, so tests run them with no cell and no task.
2. **The dedup rule is one pure function over the session table, with
   no probe before a commit** (§3.8, §4.9). The simultaneous-dial
   rule, as §4.9 words it: during the race window, the connection that
   the larger id dialed loses. The race window, from the spike: the
   two connections run in opposite directions, one dialed and one
   accepted, and the standing session was born within the window
   (30 000 ms in the spike, `simulWindowMs`). Each side measures with
   its own clock. A dead standing session always makes room. A live
   standing session outside the window keeps its place. The spike
   reaches the same winner with a different shape: its `decide` reads
   liveness with an IO call between a probe update and a commit
   update, and it re-runs the rule on a changed occupant, bounded by
   three retries. The target moves liveness into the table, so the
   whole rule runs inside one `OnceRef.update`, and the
   probe-versus-commit race disappears.
3. **Liveness is a field in the session table** (§3.8). The loop of a
   session sets it on exit, through the same update, and a dedup
   decision reads it as data. The spike calls `mux.isDead` at decision
   time; the target drops that read.
4. **The shutdown order is the §5.5 sequence**: set the closing flag →
   close the listeners → close the pending (unauthenticated)
   connections → shut down the sessions → join the session loops →
   join the host tasks. Every park names its close (PRINCIPLES 3.1,
   3.2). An upgrade read parks on the connection, and the pending-list
   close reaches it, with the 30 s deadline as the backstop (§5.4,
   from `Streams/Constants.lean`, the streams pair's home). A
   serve-loop accept parks on the listener, and the listener close
   ends it. A session accept parks on the mux session, and the session
   shutdown ends it, so `MuxSession.accept` returns `none` on close
   (the core pair). A session pump parks on its pipes, and the session
   shutdown closes them before the join.
5. **The handler registry is keyed by `ProtocolId`** (§3.10, §3.4).
   The spike keyed it by raw string; the wrapped `ProtocolId` replaces
   the string, and the literals stay in the protocol packages' id
   modules.
6. **An unknown protocol answers `na`, and the stream closes.** The
   spike's responder answers `na` for an id outside the registry and
   stays in the stream negotiation. When the negotiation lands on an
   id with no handler, the host closes the stream. The target keeps
   both steps. The negotiation over-read of the stream stage goes to
   the front of the stream (`Stream.prependBytes`, §4.7, §5.6), so
   the handler sees every coalesced byte.
7. **The host supplies the identity expectation to the upgrader**
   (§4.9; the negotiate pair's refinement). The dial path pins the
   target `PeerId`, and the listen path passes `none`. The upgrader
   compares against the completed `remotePeer` and fails with
   `Core.Error.authentication` before any muxer byte moves.
8. **Failures reach the owner as `Host.Error`, never as EOF** (§5.2,
   §3.5). The upgrader returns `Core.Error`, and the host wraps it
   once at its own boundary. An `IO.Error` fault passes underneath as
   a fault.
9. **Peerstore limits and TTLs stay deferred** (§9, delta 3). Address
   dedup at add is done, and the spike's rule stays.
10. **The keepalive probe stays open** (§9, delta 2). A session that
    dies without a write failure or a TCP EOF stays live in the table
    until its loop notices, and dedup cannot retire it earlier. The
    spike records the same gap in its `decide` docstring. This is the
    package's open work, tracked by the root delta, and it sits
    outside the W5.6 row and this unit.

## Decisions

- **Pure table updates, with no probe-then-commit** (§3.8; PRINCIPLES
  3.3). The peerstore lost addresses through get-then-set, and the
  spike's dedup raced between its probe and its commit.
  `OnceRef.update` makes the read-modify-write one step, and the pure
  rule sees the table atomically. The spike's retry-bounded
  re-evaluation is the shape the forced probe produced; the liveness
  field removes the need for it.
- **The shutdown order is a fixed sequence** (§5.5; PRINCIPLES 3.1).
  The silent-peer incident: a raw TCP client that sent nothing parked
  the upgrade responder forever, and `Host.close` joined tasks, so
  shutdown hung. The fix added a close that reaches the park, plus a
  deadline as the backstop. The order closes every park before it
  joins the task that parks in it.
- **`Host.Error` wraps `Core.Error` and adds arms of its own** (§3.5).
  The host and `cli/` match on one type. The wrapped arm keeps the
  rendered inner error for the log, and the host's own arms name the
  decisions the host makes: the gater, the empty peerstore, the
  closing flag.
- **The policy defaults live here, and `cli/` may override them**
  (§3.1's ordered-lists rule; the core pair's assignment of the
  doubles). The ordered lists are configuration, and the policy hooks
  are seams of the same shape. The permissive gater is the default
  value, and a consumer passes its own. A limiting gater is open work
  (§9, delta 4) behind the same seam.

## What the package must not depend on

- Inside libp2p, the chain puts everything below the host at its
  disposal (§2, §7 row 10). The host imports `identity` for the id and
  key types, `core` for the seam types, and `negotiate` for the
  upgrader and the stream-negotiation responder its paths call. The
  security and mux implementations
  arrive inside the configuration lists (§3.1), so a host module that
  names a concrete seam value is a review failure. Test modules import
  the test values, per PRINCIPLES 1.4.
- No `libp2p/protocols` (§2). The handler registry is the seam between
  them (§3.10): `libp2p/protocols` registers by `ProtocolId`, and the
  host dispatches without knowing a protocol.
- From the net group, `net/streams` only, for `Transport`,
  `Connection`, `Listener`, and `Stream` (§2). `net/yamux` stays
  behind the `Muxer` value of `libp2p/mux`, and no host module names
  it.
- From base, `base/conc` for `OnceRef`, `TaskSet`, `withinDeadline`,
  and `Clock` (§4.1). `base/bytes` and the codecs arrive through
  `negotiate` and `identity`, and the host names none of them
  directly.
- No crypto by name. Key material reaches the host only through the
  types of its dependencies: the private key and `PeerId` come from
  `libp2p/identity` (§2). If a refinement needs a direct import, this
  section records it as part of that refinement, per the core pair's
  rule.
