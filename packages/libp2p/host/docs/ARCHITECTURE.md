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
| `Libp2p/Host/Gate.lean` | `Gate`, a task group that refuses new tasks once its owner closes it, for the tasks that start outside any task the host owns |
| `Libp2p/Host/Swarm.lean` | `Config`, the `Host` state, `dial`, `dialPeer`, `startListening`, `newStream`, the accept loop, the upgrade pipeline, and stream serving |
| `Libp2p/Host/Shutdown.lean` | `Host.close`, the §5.5 sequence |
| `Libp2p/Host/Policy.lean` | the permissive default gater, and the permissive and denying test doubles the core pair assigned here; the default resource manager (admits everything) and the default ranker (keeps the order, no delay) |
| `Libp2p/Host/Mock/{Core,Negotiate}.lean` | the mocks of W5.2 and W5.5 until they merge (see "The mocks") |

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
  `Std.HashMap ProtocolId StreamHandler` of §3.10. The host calls the
  handler with the `StreamContext` of the session: the peer the
  upgrade proved, and the connection's remote address, which the
  session entry keeps from the upgrade. A handler failure
  closes the stream, never the session, and the error reaches the
  owner through the spawned task's completion (PRINCIPLES 3.2). This
  settles the question the core pair left open.
- `newStream` opens a stream to a peer and negotiates one of the given
  protocol ids, in preference order. With no live session, it dials
  the peer first. The answer is the selected id and the stream, with
  the bytes the negotiation over-read at its front (§4.7, §5.6). This
  is go-libp2p's `host.NewStream`
  (`vendor/go-libp2p/core/host/host.go`, lines 61 to 65). The clients
  of `libp2p/protocols` and the binaries of `cli/` reach their
  outbound streams through it.
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

## Refinements fixed at implementation (unit 1a)

The public surface leaves these points to implementation time. Unit 1a
fixes them as follows.

- **The `Host.Error` arms.** The four proposed arms stay. Three more
  name host decisions that the dial path makes: `noTransport`, no
  configured transport handles the address (`Transport.handles`, the
  streams pair); `unreachable`, the transport dialed and nobody
  listens there (`Transport.dial` answers `none`); and `dialSelf`, the
  dial targets our own id, which also keeps every dedup decision
  between two different ids. `gated` names the refusing checkpoint
  through the closed set `Checkpoint` (§3.4): `dial`, `inbound`,
  `secured`, and `resources`. go-libp2p's swarm has the same failures:
  `ErrSwarmClosed` (`vendor/go-libp2p/p2p/net/swarm/swarm.go`, line
  43), and `ErrDialToSelf`, `ErrNoTransport`, `ErrNoAddresses`, and
  `ErrGaterDisallowedConnection`
  (`vendor/go-libp2p/p2p/net/swarm/swarm_dial.go`, lines 49, 53, 60,
  and 68).
- **The session table entry.** An entry holds a session number, our
  role, the birth time on the host clock, the liveness field, and the
  session handle. The handle is a type parameter, so the table
  functions run in a test with no connection. The host draws a fresh
  number per session, and `markDead` matches it, so the exit of a
  session that dedup replaced cannot mark its successor dead.
- **The dedup function.** `dedup` returns `commit displaced` (the
  candidate took the slot; `displaced` is the live session it
  replaced, which the caller closes) or `keep standing` (the caller
  closes the candidate and serves the peer through `standing`). The
  window test is `now < born + simulWindowMs`. "Larger id" orders the
  binary form of the ids (`PeerId.toBytes`), byte by byte: both peers
  hold the same bytes, and a text order would compare the form that
  one side parsed the id in. The theorem `raceLoserAgree` proves that
  both peers drop the same connection of a race.
- **The handler ids.** The handler table lists its ids in
  `ProtocolId` order, so the stream negotiation answers the same way
  whatever the hash order.
- **The peerstore order.** The addresses of a peer keep the order
  they first arrived in, and `dialPeer` walks them in that order
  unless the address ranker reorders them.

## Refinements fixed at implementation (unit 1b)

- **The configuration and the state.** `Config` holds the identity,
  the transport list, the ordered security and muxer lists, the
  initial handlers, the gater, the resource manager, the ranker, the
  `Clock`, and `onFailure`. `Host.new` derives the local peer id from
  the identity and answers `.error` when the key derives none. The
  host's cells are the three registries, a counter for session numbers
  and pending keys, the closing flag, the listener list, and the
  pending list, each changed through `OnceRef.update` (contract 1).
- **The transport choice.** A dial or a listen uses the first transport
  of the list whose `handles` accepts the address (the streams pair,
  public surface). A trailing `/p2p/<id>` comes off first: it names
  the peer and no transport (`vendor/specs/addressing/README.md`, "The
  p2p multiaddr"), as go-libp2p's swarm drops it before its transport
  lookup (`vendor/go-libp2p/p2p/net/swarm/swarm_transport.go`, lines
  37 to 48). The component's value is the peer id's binary form, which
  `PeerId.ofBytes?` reads. An address that is only `/p2p/<id>` is
  `noTransport`.
- **The checkpoints, in go-libp2p's order.** `allowDial` before the
  dial (`vendor/go-libp2p/p2p/net/swarm/swarm_dial.go`, lines 251 and
  550); the resource manager's `openConnection` before the transport
  dial (`vendor/go-libp2p/p2p/transport/tcp/tcp.go`, line 255);
  `allowInbound`, then `openConnection`, after an accept
  (`vendor/go-libp2p/p2p/net/upgrader/listener.go`, lines 183 and
  193); and `allowSecured`, then `ConnectionScope.setPeer`, inside the
  upgrade, through `Negotiate.upgradeWith`
  (`vendor/go-libp2p/p2p/net/upgrader/upgrader.go`, line 176). A
  refusal is `gated` with the checkpoint, and the scope is released.
  The policy shapes are this unit's refinement of the core seams (the
  core ARCHITECTURE, "The policy shapes").
- **The answers of the dial path.** `dial` and `dialPeer` answer the
  peer id the handshake proved. The caller reaches the session through
  that id (`newStream`), and the host keeps the session handle. A
  live session of the expected peer answers at once, with no dial. A
  committed dial stores its transport address in the peerstore.
  `dialPeer` walks the ranker's schedule in order and waits out each
  delay on the `Clock`; the wait also wakes when `close` closes the
  shutdown channel (PRINCIPLES 3.1). With no success, it answers the
  failure of the last address.
- **Two more `Core.Error` wrappers.** `session` reports a running
  session whose join answered a failure, and `stream` reports a
  stream whose open, negotiation, or handler failed. Each wraps the
  seam error once, as `upgrade` does (§3.5).
- **Failures with no caller go to `Config.onFailure`.** An inbound
  upgrade, a session's end, and an inbound stream run in tasks that no
  caller awaits. The owner of each task reads its completion and hands
  a failure to `onFailure`, with the peer and the protocol when known,
  so a failure never reaches the owner as EOF alone (§3.5; PRINCIPLES
  3.2). A policy refusal is a decision, and goes nowhere. A fault
  passes on to the join of the task, and `close` throws it.
- **Stream serving.** The serve task of a session accepts the peer's
  streams, and each stream runs in a task that the serve task owns and
  joins when the session ends. The stream negotiates against the
  handler ids through `Negotiate.negotiateStream`, which puts the
  bytes it read past the selecting message at the front of the stream
  (§4.7). A failed negotiation, an id whose handler left the table,
  and a handler failure reset the stream; the session stays. go-libp2p
  resets a stream whose negotiation fails in the same place
  (`vendor/go-libp2p/p2p/host/basic/basic_host.go`, line 347). A
  stream the peer ends before it picks a protocol is an orderly end,
  and no failure.
- **Outbound streams.** `newStream` dials the peer through the
  peerstore when no session is live, as go-libp2p's `NewStream` calls
  `Connect` first (`basic_host.go`, line 452). It opens a stream,
  negotiates one of the caller's ids in order, and answers the
  selected id and the stream; a failed negotiation resets the stream.
  The caller owns the stream.
- **Stream shares.** Every stream takes a share from its connection's
  scope (`ConnectionScope.reserveStream`). A served stream returns it
  when its handler ends. An outbound stream returns it at a reset, or
  once our close and the peer's end have both happened. The
  connection scope's release returns every share it still holds when
  the session ends.
- **The registration race with `close`.** A path that registers a
  listener, a pending connection, or a session reads the closing flag
  after it registers, and closes what it registered when the flag is
  set. The session and host task groups are `Gate`s: a task that
  starts after `close` joined its group is refused, and the refused
  caller wakes the work and joins it itself. `Gate` lives in
  `Libp2p/Host/Gate.lean`, since a `Conc.TaskSet` keeps taking tasks
  after its join.
- **The shutdown stages.** `close` takes an optional `onStage` that
  hears each stage of §5.5 as it starts, the instrument of the unit
  1b milestone. A fault of a joined task does not stop the sequence,
  and `close` throws the first fault at the end.

## The mocks

W5.2 (`libp2p/core`) and W5.5 (`libp2p/negotiate`) have not merged,
so the package builds against mocks of their frozen surfaces (RULES.md,
"Working ahead of the tree"), under `Libp2p/Host/Mock/`. A type is a
copy of the frozen shape; an operation is `opaque`, and its body fails
with the name of the missing package. No body negotiates or opens a
session, and the mocks state no axiom. The host modules open
`Libp2p.Host.Mock`, so `Core.Error` and `Negotiate.upgradeWith` resolve
as they will against the real packages, and the integration swaps the
imports and drops the `open`. The keys and the peer id come from the
merged `libp2p/identity`.

Every upgrade runs through the negotiate mock and fails there, and the
legs also need the Noise and yamux values (W5.3, W5.4), so the unit 1b
milestones run at the integration. Unit 1a runs in full.

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
- From the codec group, `codec/multiformats` for `Multiaddr`: the
  peerstore holds addresses, and the dial path takes the `/p2p`
  component off an address. The dial path names one `base/bytes`
  function, `Bytes.ofNatList`, to give a `/p2p` component value the
  `ByteArray` form that `PeerId.ofBytes?` reads. The name arrives
  through the transitive `net/streams` import, and the host imports no
  `base/bytes` module. The other codecs arrive through `negotiate` and
  `identity`, and the host names none of them.
- From base, `base/conc` for `Async`, `OnceRef`, `TaskSet`,
  `withinDeadline`, and `Clock` (§4.1).
- No crypto by name. Key material reaches the host only through the
  types of its dependencies: the private key and `PeerId` come from
  `libp2p/identity` (§2). If a refinement needs a direct import, this
  section records it as part of that refinement, per the core pair's
  rule.
