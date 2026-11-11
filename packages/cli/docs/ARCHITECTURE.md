# leanp2p cli: architecture

`cli/` is the composition point of the stack. It holds the binaries
that assemble the ordered lists of §3.1 into a running `Host`, the
command-line and config parsing, and the interop harness (§2, "What
`cli/` is for"). It holds no protocol logic and no reusable code, and
it is disposable: a consumer project, such as the Ethereum consensus
client of §8, brings its own node binary and uses only the libraries.
The package covers root PLAN W5.8, the demo and ping binaries, and
root PLAN W5.9, the interop harness with its gate. The spike reference
is `Main.lean`, `PingNode.lean`, and `Interop.lean` (§7 row 11; §10
row 18).

## Modules

| Module | Holds, and why |
|---|---|
| `Main.lean` | the `gossipsub-interop` executable; `lakefile.toml` sets its root to `Main` |
| `Demo.lean` | the demo node, the `demo` executable; the §3.1 assembly as running code, the spike's `Main.lean` mapped here |
| `PingNode.lean` | the ping node, the `pingnode` executable; the `serve` and `dial` modes and their argument parsing |
| `GossipsubSession.lean` | the gossipsub participant's host assembly |
| `GossipsubInterop.lean` | the gossipsub participant's script driver |
| `Interop.lean` | the transport-interop harness; the host assembly and the listener and dialer modes |
| `Interop/Main.lean` | the `interop` executable's `main`, apart from `Interop.lean` so the suite can import the harness |
| `Interop/Config.lean` | the test plan's environment variables, read into a `Config`, and the timing record |
| `Interop/Resp.lean` | RESP2, pure: the reply header parse with its caps, and the command encoding |
| `Interop/Redis.lean` | the harness coordination client, private to the `interop` executable: `PING`, `RPUSH`, and `BLPOP` over one connection; the spike's `LeanP2P/Interop/Redis.lean` mapped here |

`Demo.lean` and `PingNode.lean` land with unit 1. `Main.lean` stays
the gossipsub participant. The Lake lib `Cli` is nominal: `Cli.lean`
declares no API, and the lib exists so the suite can import the
harness (see Decisions). Unit 1 widens that lib's globs for `Demo`
and `PingNode` in the commit that adds the files. Config parsing
lives in each binary, because the contracts differ. Argument parsing
uses `leanprover/lean4-cli` as the first choice. The library is
maintained under the leanprover organization, and CLAUDE.md's "Lean
on Lean" principle prefers a maintained library before a hand-rolled
one. The §2 rule bans reusable code inside `cli/`; the parsing
mechanism lives in the dependency, and each binary keeps its own
parsing code. The hand-rolled parser is the recorded fallback if the
pin does not fit the v4.34 toolchain. The tag `v4.34.0` of
`leanprover/lean4-cli` carries `lean-toolchain` `leanprover/lean4:v4.34.0`,
and its package, lib, and root module are all named `Cli`. This
package's lib and its module `Cli` use that same name, so the commit
that adds the dependency renames this lib and this empty module
together. The namespace `Cli` stays. That tag also sets
`experimental.module`. This tree has not compiled the dependency.
The harness's go-side helpers are scripts under the root `scripts/`,
test-only per CLAUDE.md's dependencies rule.

## Public surface

There is no library API for a consumer project (§2). The test suite
imports the harness. The surface of `demo`, `pingnode`, and `interop`
is the three CLI contracts. `gossipsub-interop` is the executable
rooted at `Main.lean`, and its contract stays with the gossipsub
work.

- **`demo`** (the spike's `Main.lean`, the file `Demo.lean` here).
  The executable takes no arguments. The behavior section below is
  the contract. The echo home is the open question in that section.
- **`pingnode`** (the spike's `PingNode.lean`).
  `pingnode serve <port>` hosts `127.0.0.1:<port>`, serves
  `/ipfs/ping/1.0.0` and identify, prints
  `ADDR <multiaddr> <peerid>`, and exits when stdin closes.
  `pingnode dial <multiaddr>` dials an address whose final
  `/p2p/<id>` component supplies the expected identity, pings once,
  and prints `PING OK rtt=<ms>ms`. A usage error exits 2. A runtime
  failure exits 1. The behavior section defines both.
- **`interop`** (the spike's `Interop.lean`). Configuration arrives as
  environment variables, in the shape of the libp2p
  transport-interop test plan: `transport` (`tcp`), `muxer` (`yamux`
  or `mplex`), `security` (`noise`), `is_dialer`, `ip`, `redis_addr`,
  and `test_timeout_seconds`. `Interop.startHost` offers
  `Mux.yamux` or `Mux.mplex`, the muxer named in the environment.
  The W5.9 gate still runs yamux. go-libp2p v0.50 has no mplex in
  its defaults, so the matrix skips those cells, and
  `scripts/mplex-interop.sh` covers `Mux.mplex`. The listener publishes its dialable
  multiaddr with the `/p2p/<id>` suffix through Redis, and the dialer
  fetches it, dials, pings once, and prints the timing JSON with the
  test plan's keys verbatim, `handshakePlusOneRTTMillis` and
  `pingRTTMilllis`, typo included, because the runner compares the
  JSON keys literally. Diagnostics go to stderr, and
  a failure or a timeout exits nonzero. `ip` and `redis_addr` take
  literal IPv4 addresses (see Decisions).

## Owned contracts and how the package keeps them

1. **No protocol logic.** Ping and identify come from
   `libp2p/protocols`: the handler values, `Ping.ping`, and
   `Identify.client`. The demo echo has no assigned home. The open
   question records the two documents that leave it open. Every seam
   value comes from its implementation
   package: the TCP transport from `net/streams`, which alone binds
   `Std.Async.TCP` (§9, delta 7), the security value from
   `libp2p/security`, and the muxer values from `libp2p/mux`. The
   wiring assembles and calls.
2. **No reusable code.** Code a second binary wants goes down a
   package (§2). The Redis client serves the harness alone, so it
   stays in `Interop/Redis.lean`; the first want from a second binary
   moves it down.
3. **Errors match on `Host.Error` alone** (§3.5). A binary prints the
   arm and picks its exit code, and it never matches on a lower
   package's error inductive. The behavior section names the codes,
   the stderr line, and the one map into `Host.Error`.
4. **The ordered lists are assembled here and nowhere below** (§3.1).
   No code below `cli/` hard-codes which transport or muxer exists,
   and the demo's lists are the running statement of the composition.
5. **Every exit closes and joins.** Each mode closes every host that
   `Host.new` returned before the mode returns. A fault from one
   `Host.close` still runs the close of the other host. `Host.close`
   is the shutdown order of §5.5.
6. **The RESP2 reader is capped before allocation** (§5.1,
   PRINCIPLES 2.3). The Redis client reads server-supplied line and
   bulk lengths, each read is capped, and an over-long length is an
   error. The spike's client read `readExactly n` with no cap; the
   port adds the cap. The largest value the harness reads is the
   listener's address as multiaddr text. The multiformats JSON path
   admits address text up to `maxAddressJsonBytes`, and JSON escaping
   never shortens a string, so that constant caps each reply line and
   each bulk string. An array is capped at two elements, the key and
   the value of a `BLPOP` answer. The theorems
   `parseHeaderBulkOverCap` and `parseHeaderArrayOverCap` state both
   caps on the header parse.

## W5.8 behavior

This section binds the demo and the ping node. Unit 1 implements it.
The open question at the end has no home yet. The interop contract
above stays in force.

### Executables

| Executable | File | Module | Lake root |
|---|---|---|---|
| `demo` | `Demo.lean` | `Demo` | `Demo` |
| `pingnode` | `PingNode.lean` | `PingNode` | `PingNode` |

Both files sit in `packages/cli`. The namespaces are `Cli.Demo` and
`Cli.PingNode`, the shape `Cli.GossipsubSession` already uses.
`gossipsub-interop` keeps the root `Main`. `interop` keeps the root
`Interop.Main`. Unit 1 adds the two `lean_exe` entries. The current
`lakefile.toml` has neither name.

### Arguments

`demo` takes an empty argument list. Any argument is a usage error.

`pingnode serve` takes one port. `pingnode dial` takes one multiaddr.
A missing subcommand, an unknown subcommand, a missing operand, and
an extra operand are usage errors.

A usage error prints one line to stderr and exits 2. The process has
created no host.

The text `0` is a valid port. Any other valid text starts with a
digit from `1` to `9`, uses only digits, and names a value through
65535. `startListening` returns the address the kernel bound for
port 0, and the `ADDR` line prints that address. Any other port
text is a usage error.

`dial` parses the operand with `Multiaddr.parse?`. A parse failure
is a usage error. The stderr line is the failure text and the
operand.

The last component of a dial address is `/p2p/<id>`.
`Host.splitPeer` returns the transport address and a `PeerId`. A
missing final component, a peer component in another position, an
address whose only component is `/p2p/<id>`, and any other
`splitPeer` failure are usage errors. The dial then uses that peer
id as the expected identity. A port of 0 inside a parsed dial
address reaches the transport, and the transport reports the result
as a runtime failure.

### Exit status

Success exits 0. A usage error exits 2. A runtime failure exits 1.

Contract lines go to stdout. Diagnostics go to stderr. The peer id
text is `PeerId.toString`. The address text is `Multiaddr.toString`.
The same-peer check compares `a.hash == b.hash` (`PeerId.lean`,
"Comparing peer ids").

A runtime failure is a `Host.Error`, an initialization failure, or a
thrown `IO.Error`.

Initialization is `Crypto.ed25519Generate`, then
`PrivKey.ofData? .ed25519`, then `Noise.Config.generate`, then
`Host.new`. Each step returns its own error. The stderr line is the
rendered value. `Host.new` answers `Identity.Error` when the key
derives no peer id.

`startListening`, `dial`, `dialPeer`, and `newStream` answer
`Host.Error`. The stderr line is `Host.Error.render`. `Host.close`
throws the first fault of a joined task (`Shutdown.lean`). That
throw is the fault channel.

`Ping.ping` answers `Ping.Error`. `Identify.client` answers
`Identify.Error`. The exchange wrapper maps the first through
`Ping.mapPingError` and the second through `Identify.mapIdentifyError`,
then wraps the `Core.Error` as `Host.Error.stream`. The command
matches that `Host.Error`.

`Identify.client` answers `.ok none` when the stream ends before any
byte (`Identify.client`). That value stays the end-of-stream channel
of §3.5. The demo prints one stderr line and exits 1.

`Ping.ping` records that the echo path answers `.ok (some rtt)`. An
`.ok none` from that call takes the same exit as the identify
`none`.

A thrown `IO.Error` stays a fault. The binary prints it, closes the
hosts it created, and exits 1.

### Composition

Both binaries build one `Host.Config`.

- The identity is a fresh Ed25519 key from the two calls above.
- `transports` is `[Streams.Tcp.transport]`.
- `security` is `[Noise.securityProtocol cfg]`.
- `muxers` is `[Mux.yamux, Mux.mplex]`. That order is the mux
  architecture and root §8.
- The gater, the resource manager, the ranker, and the clock keep
  the defaults on `Host.Config`.
- `onFailure` prints `Host.Error.render` to stderr, and it includes
  the peer and the protocol when the failure carries them. A policy
  refusal stays inside the host (the host architecture, Decisions).
  One inbound failure leaves the accept loop running. A fault of a
  host task surfaces when `Host.close` joins the task.

The demo and the ping node register ping and identify. Echo
registration waits on the open question.

`Identify.respondHandler` is registered after `startListening`
returns. Its listen-address list is that bound address, as
`Multiaddr.toBytes`. Its protocol list is the ids just registered,
each through `ProtocolId.toString`. The agent string is `leanp2p`.
The observed address stays the `StreamContext` value inside
`respondHandler`. The protocol version stays
`Constants.identifyProtocolVersion`, which `respond` writes.

The demo's identify client requires three facts in the record. The
derived peer hash equals the dialed peer hash. The bound address is
present. Every registered protocol id is present. A missing fact
exits 1.

### Deadlines

The upgrade deadline stays in the host. `upgrade` in
`Libp2p/Host/Upgrade.lean` runs `Conc.withinDeadline` for
`Streams.unauthDeadlineMs`, and the expiry hook is
`Connection.closeQuietly`.

`Identify.client` takes a timeout and resets the stream when the
timeout expires. The demo passes `Streams.unauthDeadlineMs`. The ping
node serves identify and makes no identify client call.

`Ping.ping` sends `Constants.pingSize` bytes from `Crypto.randomBytes`
and waits on the echo with the stream's own read. A generator
failure is a fault. The caller
wraps that call in `Conc.withinDeadline` for
`Streams.unauthDeadlineMs`. The duration is that constant, whose home
stays `net/streams`.
The bound covers the exchange, and it starts once `newStream` has
returned that stream. §5.4 leaves an authenticated idle connection
open. Expiry resets the stream, and the connection stays up.

The expiry hook is the one in `Identify.readFrame`. `onExpiry` has
type `BaseIO Unit`, and `Stream.reset` is `Async`, so the wrapper
spawns `s.reset` on a `TaskSet` that the call owns and joins after
the race. `Stream.close` ends the write direction. The parked read
wakes from `Stream.reset`.

On yamux, `Yamux.Core.resetLocal` ends both directions. The loop
action `.endWrites` wakes a writer parked on credit, and `.reset`
wakes a reader (`Yamux/Loop.lean`). On mplex, `Port.abort` closes
the inbox and wakes a parked read. A queued mplex write receives
the reset when the writer finds the stream closed for writing
(`Mplex/Session.lean`).

`Conc.Error.deadlineExpired` maps to
`Host.Error.stream (.timeout ...)`. `Conc.Error.closed` maps to
`Host.Error.stream (.closed ...)`.

`Ping.pingHandler` parks until the stream ends or the session ends.
`Host.close` shuts the sessions down. The
serve task records that the session end wakes a handler parked on
its read (`Swarm.serveSession`).

### Stream opening

`Host.newStream` dials through `dialPeer` when no session is live
(`Swarm.newStream`). `dialPeer` dials through `dialAddr`, and
`upgradeConn` runs `upgrade`. `upgrade` bounds that dial with
`withinDeadline` and `Connection.closeQuietly`. A live session skips
the dial.

The call then opens a mux stream and runs `negotiateStream`. The
answer is the selected id and the stream. `openStream` parks on the
session until the session answers the open. `negotiateStream` then
parks on `stream.read` while the peer sends nothing on that stream
(`StreamSelect.lean`). The module records that no measure bounds
that loop. The caller holds the stream only after the selection.

The exchange deadline starts after that return. It resets the stream
the caller holds, and the connection stays up.

A session close reaches a parked stream read. Yamux `teardown`
closes every stream inbox (`Yamux/Loop.lean`). Mplex `endStreams`
aborts every port (`Mplex/Session.lean`). `Host.close` closes each
live session and then joins the session tasks (`Shutdown.lean`).
The host keeps the session handle. The close the CLI can call is
`Host.close`.

`Host.close` closes the listeners and every session of that host.
§5.4 leaves an authenticated idle connection open. A command closes
a host it owns after the command has failed. `withinDeadline` can
take `newStream` as its work. `onExpiry` has type `BaseIO Unit`, and
`Host.close` is `Async`. A result that arrives after the timer can
hold the stream. `release` frees a value the caller never sees, and
the default `release` drops the value (`Conc/Deadline.lean`).

### Open question: the deadline around `Host.newStream`

Which close may a timer around `Host.newStream` run, and which
duration does it use? During negotiation the caller holds no stream.
The exchange reset runs on the stream the call has returned. The
upgrade deadline covers the dial that runs when no session is live.
`Host.close` wakes a read parked in the session through the session
close, and the same call ends the host. No current contract assigns
this timer. An answer has to name the close and the duration before
the dial or the demo adds one.

The question blocks a negotiation bound on `pingnode dial` and on
each `newStream` of the demo. `pingnode serve` opens no outbound
stream.

The question for the issue:

What bounds protocol negotiation inside `Host.newStream`? The stream
returns only after `negotiateStream` finishes, and that read parks
while an authenticated peer stays silent on the stream
(`Libp2p/Host/StreamSelect.lean`). The CLI holds no stream to reset
until the call returns. `Host.close` closes the session and wakes
parked stream reads, and it also ends the host. May `pingnode dial`
and the demo start that close from a timer around `newStream`, and
what duration applies?

### Stream retirement

`newStream` returns the stream to its caller (`Swarm.newStream`).

On success the caller uses `Stream.close`, after the exchange has
its bytes. Ping closes after the echo check. Identify closes after
the client holds the record. `respondTo` has already half-closed
the responder.

On a protocol failure the caller uses `Stream.reset`. On a timeout
the expiry hook has already reset the stream. On a fault the caller
resets the stream when the stream exists, and the fault propagates
after that reset. The success path is the path that calls
`Stream.close`.

### Server lifetime

These rules bind `pingnode serve`.

The mode registers identify with the bound address, prints `ADDR`,
and flushes stdout. The flush follows a successful listen and that
registration. While stdin stays open, the process accepts a dial and
serves it. The unit 1 check covers that dial with
`LEAN_NUM_THREADS=1`, and again under `+RTS -N1`.

Stdin EOF is the shutdown signal. `Handle.lines` in the v4.34
`Init/System/IO.lean` stops when `getLine` returns an empty string,
and the spike's serve loop treats that empty result as EOF. The loop
discards each line. The bytes belong to the operator, so the §5.1
caps stay on the peer frames. After EOF the mode calls `Host.close`
and exits.

An inbound peer failure reaches stderr through `onFailure`. The
accept loop keeps running. A host-task fault reaches stderr when
`close` throws it, and the process then exits 1.

The read's scheduling is an implementation choice, and this slice has
not run it. `IO.asTask` defaults to `Task.Priority.default`
(`Init/Core.lean`). Priorities through `Task.Priority.max` run on the
shared worker pool. `Task.Priority.dedicated` asks for a separate
thread. The unit 1 dial check is what shows whether the chosen
priority keeps the accept loop moving under one pool worker.
`scripts/park-threads.lean` measures `IO.wait`.

A task that runs the read ends when `getLine` returns or throws. The
owner joins the task after that return, and then calls `Host.close`.
`Host.close` closes listeners, pending connections, and sessions
(`Shutdown.lean`). The sequence leaves stdin open. A cleanup path
joins the reader after that return. The read stays an `IO` action. A
blocking call inside `Async` holds a pool worker (the conc
architecture, Decisions).

### Demo lifetime

The demo runs these steps in order.

1. Generate two Ed25519 identities.
2. Build two hosts.
3. Register ping on the listener.
4. Listen on `/ip4/127.0.0.1/tcp/0`.
5. Register identify with the bound address and the ids registered
   so far.
6. Store that address with `addAddrs`, then `dialPeer`.
7. Open a `newStream` for ping, then identify. The echo stream waits
   on the open question.
8. Close the dialer, then the listener.

Every exit closes each host that `Host.new` returned. The call is
`Host.close`. A fault from the first close still runs the second
close. The process exits 1 with the first fault. A demo that
received `onFailure` also exits 1, after both closes.

On success, stdout carries the dial line, the ping rtt, and the
identify summary. The spike's `Main.lean` is the shape of those
lines. The echo line waits on the open question.

### Open question: the demo echo home

The demo exchange includes an echo. The spike's `Main.lean` registers
`/demo/echo/1.0.0` on the listener, reads one chunk, writes those
bytes, and half-closes. The client writes `echo-me` and reads the
reply.

§2 keeps protocol logic out of `cli/`. §4.9 names identify, ping,
req/resp, and gossipsub. The protocols architecture follows that
list, and the package exports no echo handler. `Tests/Host.lean`
keeps a private handler for `/test/echo`.

Issue #22 and PR #50 assign no home. The review of PR #50 on 6
November 2026 records the CLI sentence "echo must come from protocol
test support" under "Checked, no change needed." The merged protocols
package has no such support.

The implementation slice places the handler and the client after a
maintainer assigns the home. The ping node registers ping and
identify.

The question for the issue:

Where does the W5.8 demo echo handler live, and where does its client
live? `cli/` holds no protocol logic (§2). `protocols/` lists
identify, ping, req/resp, and gossipsub (§4.9) and exports no echo
handler. The spike demo still echoes on `/demo/echo/1.0.0`.

## Decisions

- **A nominal lib, and no public API.** §2 gives `cli/` no public
  API, and the dependency chain of §2 puts it where nothing below
  can import it. `Cli.lean` declares nothing. The Lake lib `Cli`
  exists so the suite can import `Interop` and the gossipsub
  modules. Its current roots are `Cli`, `Interop`,
  `GossipsubInterop`, and `GossipsubSession`.
- **The go-side helpers stay scripts, test-only.** CLAUDE.md's
  dependencies rule keeps Go and Rust tooling test-only, confined to
  the harness, and never on a shipped or proof path. The tree holds
  `interop-matrix.sh` and `interop-slowreader/` under the root
  `scripts/`, beside the W0.3 vector tooling (§7 row 11's note).
  Unit 1 adds `pingd.go` and `ping-interop.sh`, in the spike's
  ping-interop shape. The spike also kept a
  test-plans runner image, `interop/leanp2p/{Makefile,Dockerfile}`.
  The target drops the image, and `scripts/interop-matrix.sh` is the
  gate's only form, so docker appears only inside the scripts.
- **The matrix's go peer is go-libp2p's own test-plan program.** The
  test plan builds its go image from go-libp2p's `test-plans/`
  directory with `PingDockerfile`
  (`vendor/test-plans/transport-interop/impl/go/v0.48/Makefile`, line
  7). The script builds the same program from `vendor/go-libp2p` at
  the pinned v0.50.0, so the peer across the wire is the one the
  test plan runs. The slow-reader program joins that module, with its
  `go.mod` and `go.sum`.
- **The listener publishes the local address of its Redis
  connection.** go's peer publishes its first address that is not
  loopback, from the host's interface list
  (`vendor/go-libp2p/test-plans/cmd/ping/main.go`, lines 202 to 209).
  The Lean runtime has no interface list. When `ip` is `0.0.0.0`, the
  harness takes the IP of its Redis connection's local address: the
  kernel picked it to reach the server that both peers share, so the
  dialer reaches it too. A concrete `ip` is published as given.
- **`redis_addr` is a literal IPv4 address.** The test plan defaults
  it to the host name `redis` (`vendor/test-plans/transport-interop/README.md`,
  line 26). Root §4.1 keeps `Std.Async`, and so its DNS resolver, out
  of every package but `base/conc`, and the TCP transport dials `/ip4`
  and `/ip6` only (the streams ARCHITECTURE, "Public surface"). A host
  name is a configuration error with its own message. The gate runs
  only through `scripts/interop-matrix.sh`, which passes literal
  addresses.
- **The demo composition doubles as the composition documentation**
  (root §2: "shows, as running code, how to compose the stack"). A
  reader who wants to compose the stack reads `Demo.lean`.

## The stack

The harness composes the real packages: an Ed25519 identity from
`Libp2p.Identity`, the TCP transport, `Noise.securityProtocol` with a
static key from `Noise.Config.generate`, one muxer from the test
plan, `Libp2p.Host`, and ping's handler and initiator from
`Libp2p.Protocols.Ping`. The demo and the ping node use that same
identity, transport, and Noise construction, and their muxer list is
`[Mux.yamux, Mux.mplex]`.

## What the package must not depend on

- Everything below is allowed, because §2 puts `cli/` at the left end
  of the chain. The rule that binds is the reverse: nothing below may
  import it, and no module in it may hold logic that a library wants.
- One new external dependency, `leanprover/lean4-cli`, for argument
  parsing. CLAUDE.md's dependency rule records it: the require block,
  `lake update`, the pinned rev, and `lake-manifest.json` committed.
  The candidate pin is tag `v4.34.0`. The modules section records the
  `Cli` name collision and that this tree has not compiled the pin.
  The hand-rolled parser is the recorded fallback if the pin does not
  fit v4.34, and the argument behavior above is the same on either
  route. The coordination client is in-repo Lean, as the spike's
  is, with no Redis client package.
- No build glue. The executables build through the declarative
  package metadata (PRINCIPLES 4.2).
