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

`Demo.lean` and `PingNode.lean` are the executable roots. Each
`main` checks its arguments with `Cmd.parse`. A usage error exits 2.
An empty `demo` list runs the loopback exchange and exits 0.
`pingnode serve` listens. `pingnode dial` dials the expected peer
and prints one ping.
`Main.lean`
stays the gossipsub participant. The Lake lib is `CliHarness`.
`CliHarness.lean` declares no API, and the lib exists so the suite
can import the harness (see Decisions). Its globs include `Demo`
and `PingNode`. Config parsing lives in each binary, because the
contracts differ. Argument parsing uses `leanprover/lean4-cli`.
The library is maintained under the leanprover organization, and
CLAUDE.md's "Lean on Lean" principle prefers a maintained library
before a hand-rolled one. The §2 rule bans reusable code inside
`cli/`; the parsing mechanism lives in the dependency, and each
binary keeps its own parsing code. The hand-rolled parser remains
the recorded fallback if a later pin fails the v4.34 toolchain.
The tag `v4.34.0` is commit
`e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`. Its `lean-toolchain` is
`leanprover/lean4:v4.34.0`, and its package, lib, and root module
are all named `Cli`. An isolated consumer imported `Cli`, built a
`Cmd`, and called `validate` on this toolchain, and that build
completed. This package's lib and empty root are `CliHarness`, so
the module name `Cli` belongs to the parser. The namespace `Cli`
stays. That tag sets `experimental.module`. Each executable parses its own arguments. The harness's go-side helpers are scripts
under the root `scripts/`, test-only per CLAUDE.md's dependencies
rule.

## Public surface

There is no library API for a consumer project (§2). The test suite
imports the harness. The surface of `demo`, `pingnode`, and `interop`
is the three CLI contracts. `gossipsub-interop` is the executable
rooted at `Main.lean`, and its contract stays with the gossipsub
work.

- **`demo`** (the spike's `Main.lean`, the file `Demo.lean` here).
  The executable takes no arguments. The behavior section below is
  the contract. The echo home is the working decision in that
  section. This slice does not add the module.
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
   `Identify.client`. The demo echo home is
   `Libp2p.Protocols.TestSupport.Echo`, recorded below. That module
   provides the handler and the client. The demo executable
   wires them. Every seam
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
The echo home at the end is the working decision. The interop
contract above stays in force.

### Executables

| Executable | File | Module | Lake root |
|---|---|---|---|
| `demo` | `Demo.lean` | `Demo` | `Demo` |
| `pingnode` | `PingNode.lean` | `PingNode` | `PingNode` |

Both files sit in `packages/cli`. The namespaces are `Cli.Demo` and
`Cli.PingNode`, the shape `Cli.GossipsubSession` already uses.
`gossipsub-interop` keeps the root `Main`. `interop` keeps the root
`Interop.Main`. `lakefile.toml` names `demo` and `pingnode`. The
argument table below is in force. An empty `demo` list runs the
loopback exchange. `pingnode serve` listens.
`pingnode dial` dials the expected peer and prints one ping.

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
`Host.splitPeer` returns the transport address and a `PeerId`.
`splitPeer` removes only that trailing component. A `p2p` component
that remains in the transport prefix is a usage error. A missing
final component, a peer component in another position, an address
whose only component is `/p2p/<id>`, and any other `splitPeer`
failure are usage errors. The dial uses that address and that
peer id as the arguments of `Host.dial`. A port of 0 inside a
parsed dial address reaches the transport, and the transport
reports the result as a runtime failure. `Tests/Cli.lean` covers
that address with `capture` and a 10 second deadline. The child
exits inside the deadline, the exit code is 1, stdout is empty, and
stderr is a nonempty runtime diagnostic. The kernel text stays with
the transport. `Tests/CliLive.lean` covers a port the test closed
and matches `nobody listens at <addr>`.

The commands are `Cmd.init` values with an empty flag list, so help
and version flags are absent. `Cmd.parse` answers the parser error.
A usage line is that message, `reprStr` of a `Multiaddr.parse?`
error followed by the operand, `Host.Error.render` of a `splitPeer`
error followed by the operand, or `dial address has an earlier /p2p
peer:` followed by the operand. `.ok (_, none)` from `splitPeer` is
a usage error. A newline in an operand is written as `\n`, and a
carriage return as `\r`, before the line is printed. The process
creates no host.

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

### Usage

`lake build` writes `.lake/build/bin/demo` and
`.lake/build/bin/pingnode`.

`demo` takes no arguments.

```
.lake/build/bin/demo
```

Success prints four lines and exits 0. The peer id and the round-trip
time belong to that run.

```
dialed <peer id> (noise + yamux, remote verified)
ping rtt: <ms> ms
identified: <peer id>, 1 addr(s), 3 protocol(s)
echo: echo-me
```

`pingnode serve 0` asks the kernel for a loopback port. The process
prints one line and leaves stdin open.

```
.lake/build/bin/pingnode serve 0
```

```
ADDR /ip4/127.0.0.1/tcp/<port> <peer id>
```

A second terminal builds the dial address from that line. The address
is the `ADDR` address field, then `/p2p/`, then the peer field.

```
.lake/build/bin/pingnode dial /ip4/127.0.0.1/tcp/<port>/p2p/<peer id>
```

A successful dial prints one line and exits 0.

```
PING OK rtt=<ms>ms
```

The server keeps serving while its stdin stays open. EOF stops it.
In a terminal, Ctrl-D sends that EOF. The server then calls
`Host.close` and exits 0.

The demo writes its four lines with `putStr` and `flush`. A closed
stdout throws inside `demo`. `guarding` then closes both hosts and
exits 1. `pingnode serve` flushes `ADDR` after listen, as the server
lifetime section records.

Exit 0 is success. Exit 2 is a usage error, and the process has
created no host. Exit 1 is a runtime failure. Contract lines go to
stdout. Diagnostics go to stderr.

### Composition

Both binaries build one `Host.Config`.

- The identity is a fresh Ed25519 key from the two calls above.
- `transports` is `[Streams.Tcp.transport]`.
- `security` is `[Noise.securityProtocol cfg]`.
- `muxers` is `[Mux.yamux, Mux.mplex]`. That order is the mux
  architecture and root §8.
- The gater, the resource manager, the ranker, and the clock keep
  the defaults on `Host.Config`.
- `onFailure` writes `Host.Error.render` to stderr in the host task
  that saw the failure, and it includes the peer and the protocol
  when the failure carries them. The write finishes before that task
  ends. `Host.close` joins the task. A write that throws is kept
  as an `IO.Error`, and the process exits 1 after `close`. The demo
  also records that the callback ran. That flag is not an
  `IO.Error`. The Demo lifetime section reads it after both closes.
  `pingnode serve` does not keep that flag. A policy refusal stays inside
  the host (the host architecture, Decisions). One inbound failure
  leaves the accept loop running. A fault of a host task surfaces
  when `Host.close` joins the task.

The demo and the ping node register ping and identify. The demo
also registers `Libp2p.Protocols.TestSupport.Echo.handler`.

`Identify.respondHandler` is registered after `startListening`
returns. Its listen-address list is that bound address, as
`Multiaddr.toBytes`. Its protocol list is the ids just registered,
each through `ProtocolId.toString`. The agent string is `leanp2p`.
The observed address stays the `StreamContext` value inside
`respondHandler`. The protocol version stays
`Constants.identifyProtocolVersion`, which `respond` writes.

`Identify.client` receives `some peer` and validates that peer. The
demo then requires the bound address and every registered protocol
id. A missing fact exits 1.

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

### Working decision: the deadline around `Host.newStream`

This branch selects a contributor working decision. The review
context is
https://github.com/etheorem/leanp2p/issues/22#issuecomment-6805941244.

During negotiation the caller holds no stream. The stream returns
only after `negotiateStream` finishes, and that read parks while an
authenticated peer stays silent
(`Libp2p/Host/StreamSelect.lean`). `Host.close` closes the session
and wakes parked stream reads.

One-shot `pingnode dial` and `demo` apply `Streams.unauthDeadlineMs`
(30 seconds) around `Host.newStream`. Expiry fails the command and
closes the host that command owns. The command joins its work and
its cleanup tasks. A result that arrives after the timer goes to
`release`.

The policy adds no library idle timeout. `Host` keeps its interface.
An authenticated idle connection stays open under §5.4.
`pingnode serve` opens no outbound stream. `pingnode dial`
implements the timer. `demo` applies the same budget to each
`newStream`, and to the ping and echo exchanges. Identify passes
the same duration to `Identify.client`.

### Dial

`validDial` returns the parsed multiaddr and the expected `PeerId`.
`dial` passes that pair to `Host.dial`. The `some` peer is the
expected identity `checkIdentity` compares during the upgrade.

The command then opens one ping stream with `Host.newStream`.
`Conc.withinDeadline` applies `Streams.unauthDeadlineMs` around that
call. The clock is `Clock.system`. Expiry spawns `Host.close` on a
`TaskSet` the command owns. The close wakes the parked open. The
command joins the open and the cleanup set. `release` resets a
stream that arrives after the timer. The default `release` drops its
value, and a stream needs this reset.

An `IO.Error` from the open starts the same close, and the command
joins it. The thrown error stays the first fault. An `Except`
failure from `newStream` returns that `Host.Error`. `guarding` then
closes the host. `Host.close` is idempotent, so the expiry close and
the later `guarding` close both run.

The payload comes from `Crypto.randomBytes` at `Ping.payloadSize`.
`Ping.ping` runs under a second `withinDeadline` of the same
duration. That budget starts after `newStream` returns. Expiry
resets the stream. A protocol failure resets the stream and maps
the error through `Ping.mapPingError` into `Host.Error.stream`. A
thrown `IO.Error` stays a fault. Success calls `Stream.close`, then
prints `PING OK rtt=<ms>ms`. The process prints that line only after
the echo check.

A usage error exits 2. Success exits 0. A runtime failure or a
cleanup failure exits 1. Every host `openHost` returns reaches
`Host.close`.

`Tests/CliLive.lean` covers a successful dial, a port the test
bound and then closed, an expected-peer mismatch, a peer that stays
silent during protocol selection, and a peer that reads the payload
and writes no echo. The two silent peers run until the command
budget. The capture bound is 50 seconds, and the command exits
inside it. Stdout is empty on each failure before a successful ping.
The refused dial prints `nobody listens at <addr>`. The mismatch
prints `upgrade failed: authentication failure: remote peer id
differs from the expected peer id`. The silent selection prints
`stream failed: timeout: the stream opening deadline expired`. The
missing echo prints `stream failed: timeout: the ping exchange
deadline expired`.

The dial slice recorded `lake build demo pingnode tests`, then
`LEANP2P_SUITE=cli .lake/build/bin/tests` and `LEANP2P_SUITE=cli
LEAN_NUM_THREADS=1 .lake/build/bin/tests +RTS -N1 -RTS`. Each of
those suite runs passed 137 checks, with 0 failed, 0 todo, and 0
skipped. The port-zero correction builds with `lake build tests`.
`LEANP2P_SUITE=cli LEAN_NUM_THREADS=1 .lake/build/bin/tests +RTS -N1
-RTS` passed 138 checks, with 0 failed, 0 todo, and 0 skipped. That
command runs the CLI suites alone. The added check is the bounded
port-zero exit. `scripts/lint-imports.sh` checked 189 module files,
with 0 violations. `git diff --check` reported no whitespace errors.
The serve slice's focused command passed 121 checks. The full
`lake test` was not rerun. Its recorded baseline still has one
failure in `Tests/Streams.lean`: `the teardown aborted the stuck
write: the peer meets a reset`.

`demo` runs the two-host loop and exits 0. The Lean-to-Go ping
check is recorded in the Go-helper decision. The bidirectional
gate stays unfinished. The abrupt Go-first close stays the historical
case in the Go-helper decision.

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
serves it. `Tests/CliLive.lean` covers that dial with
`LEAN_NUM_THREADS=1`.

Stdin EOF is the shutdown signal. The mode calls `Handle.getLine` on
stdin in `IO`, after the flush, and outside `Async`. An empty string
is EOF. Any other line is discarded. The bytes belong to the
operator, so the §5.1 caps stay on the peer frames. After EOF the
mode calls `Host.close` and exits 0, unless that close throws. A
thrown `IO.Error` from the read or from the flush exits 1, and that
path calls `Host.close` too.

An inbound peer failure reaches stderr through `onFailure`, on the
host task that saw it. The accept loop keeps running. A write that
throws is kept until `close` returns, and the process then exits 1.
A host-task fault reaches stderr when `close` throws it, and the
process then exits 1. An abrupt Go close after a successful ping
can take this path. The coordinated Go-to-Lean check closes this
stdin first, while the Go host is still up. The Go-helper decision
records both lifecycles.

The read has no reader task. The calling thread blocks in `getLine`.
The accept loop is the host task that `startListening` started.
`Tests/CliLive.lean` reads `ADDR` while stdin stays open, completes
ping and identify, and then closes stdin. The server exits inside
the test timeout. `Host.close` leaves stdin open. A blocking call
inside `Async` holds a pool worker (the conc architecture,
Decisions), so this read stays in `IO`. The focused command
`LEANP2P_SUITE=cli LEAN_NUM_THREADS=1 .lake/build/bin/tests +RTS -N1 -RTS`
passed 121 checks, with 0 failed, 0 todo, and 0 skipped. That
command runs the CLI suites alone. The full `lake test` was not
rerun for this slice. Its recorded baseline still has one failure
in `Tests/Streams.lean`: `the teardown aborted the stuck write:
the peer meets a reset`.

### Demo lifetime

The demo runs these steps in order.

1. Generate two Ed25519 identities.
2. Build two hosts.
3. Register ping and `Libp2p.Protocols.TestSupport.Echo.handler`
   on the listener.
4. Listen on `/ip4/127.0.0.1/tcp/0`.
5. Register identify with the bound address and the three ids:
   ping, `/demo/echo/1.0.0`, and identify.
6. Store that address with `addAddrs`, then `dialPeer`.
7. Open a `newStream` for ping, then identify, then the echo id.
   Each open uses the 30 second budget above. Expiry closes the
   dialer. The command still closes the listener.
8. Close the dialer, then the listener.

The listener is owned as soon as its `Host.new` returns. A failure
while the dialer is built closes that listener, and the dialer's
fault stays the stderr line. Every later exit closes the dialer,
then the listener. The call is `Host.close`. A fault from the first
close still runs the second close. The process exits 1 with the
first fault.

`reportFailure` sets `reported` before it writes the line. The flag
stays set when the write succeeds. A thrown write is stored in
`writeFault` and does not clear the flag. The command does not build
an `IO.Error` from the `Host.Error`. `guarding` reads both fields
after `closeBoth`. That close joins the tasks that called the
callback, so the read sees the finished callback. `exitAfterCleanup`
returns 1 when `reported` is set, when `writeFault` is set, or when
the body or a close already failed. A stored write fault is printed
only when that earlier code is still 0. A line already printed stays
the stderr line.

`reportFailure`, `closeBoth`, and `guarding` are private. The
executable has no injection flag, so the process checks cannot
deliver a `Failure` through `onFailure`. The examples on
`exitAfterCleanup` cover a reported callback after a successful body,
a stored write fault, both together, a failed body, and a clean
success. The trace above is the path from the callback through both
closes to that status.

On success, stdout carries four lines. The spike's `Main.lean` is
the shape. The peer id text is `PeerId.toString`.

```
dialed <peer id> (noise + yamux, remote verified)
ping rtt: <ms> ms
identified: <peer id>, 1 addr(s), 3 protocol(s)
echo: echo-me
```

The identify line counts the one bound address and the three
registered protocol ids. The echo line follows a reply equal to the
bytes of `echo-me`. Stderr is empty. The process exits 0.

### Working decision: the demo echo home

This branch selects a contributor working decision. The review
context is
https://github.com/etheorem/leanp2p/issues/22#issuecomment-6805941244.

The handler and the client live at
`Libp2p.Protocols.TestSupport.Echo`, below `cli/`. The protocol id
is `/demo/echo/1.0.0`, in that one module. The value is a
`StreamHandler`. The executable imports the value and holds no echo
logic.

§2 keeps protocol logic out of `cli/`. The review of PR #50 on 6
November 2026 records "echo must come from protocol test support."
§4.9 still names identify, ping, req/resp, and gossipsub. Test
support sits beside that list. The spike handler reads one chunk,
writes those bytes, and half-closes. The client writes one payload and reads one reply.
`Libp2p.Protocols.TestSupport.Echo` provides `serve`, `handler`, and
`exchange`. The protocol id lives in that module. An initial EOF
half-closes and returns. A `Streams.Error` maps through
`mapStreamError`. A thrown `IO.Error` stays thrown. The caller owns
the stream. `serve` half-closes on an orderly read. `exchange` leaves
the stream open. One chunk is the whole exchange. The demo chooses
the payload and prints the result. The demo sends the bytes of
`echo-me`, requires the same bytes back, and prints `echo: echo-me`.
A later chunk stays unread. The ping node registers ping and identify.

`lake build tests` completed. `LEANP2P_SUITE=protocols
.lake/build/bin/tests` passed 80 checks, with 0 failed, 0 todo, and
0 skipped. `LEANP2P_SUITE=protocols LEAN_NUM_THREADS=1
.lake/build/bin/tests +RTS -N1 -RTS` passed 80 checks, with 0 failed,
0 todo, and 0 skipped. That command runs `Tests.Protocols`.
`scripts/lint-imports.sh` checked 190 module files, with 0
violations. `git diff --check` reported no whitespace errors. The
138-check CLI result stays the dial slice's record.

`lake build demo pingnode tests` completed. `LEANP2P_SUITE=cli
.lake/build/bin/tests` passed 140 checks, with 0 failed, 0 todo, and
0 skipped. `LEANP2P_SUITE=cli LEAN_NUM_THREADS=1 .lake/build/bin/tests
+RTS -N1 -RTS` passed 140 checks, with 0 failed, 0 todo, and 0
skipped. That command runs `Tests.Cli` and `Tests.CliLive`. The
success check requires the four lines above, empty stderr, and exit
0. A closed stdout exits 1 inside 30 seconds, with a nonempty stderr.
`scripts/lint-imports.sh` checked 190 module files, with 0
violations. `git diff --check` reported no whitespace errors. The
reviewer independently reproduced that 140-check result. After the
callback correction, `lake build demo pingnode tests` completed.
`LEANP2P_SUITE=cli LEAN_NUM_THREADS=1 .lake/build/bin/tests +RTS -N1
-RTS` passed 140 checks, with 0 failed, 0 todo, and 0 skipped. The
success check and the closed-stdout check stay in that run. The
callback examples are checked when `demo` builds. The 80-check
result stays the echo suite's record. That callback correction did
not rerun the full `lake test`. The gate record for `f994be4`
records the later full runs. The W5.9 gate and issue #22 stay open.

### Gate record for `f994be4`

This record is the local suite that included the demo flush, and the
GitHub checks on `f994be4` before that flush was published. The
140-check commands above run `Tests.Cli` and `Tests.CliLive` only.

`lake build` exited 0. Its log has no warning line.
`scripts/lint-imports.sh` exited 0 and checked 190 module files, with
0 violations. `lake test` exited 1: 28095 passed, 1 failed, 0 todo,
and 7 skipped. `lake test -- +RTS -N1 -RTS` exited 1 with the same
summary. The failure is `Tests/Streams.lean` line 985, `the teardown
aborted the stuck write: the peer meets a reset`. The CLI sections
of those runs are not a full pass. GitHub `build-and-test` on
`f994be4` failed `demo closed stdout exits` and `demo closed stdout
stderr` during `lake test`, then skipped the one-worker suite, the
import lint, and vector provenance. Those two checks predate the
demo flush.
`scripts/ping-go-interop.sh` exited 0 with `PASS go-to-lean PING OK
rtt=710.459µs`. `scripts/ping-go-interop.sh lean-to-go` exited 0 with
`PASS lean-to-go PING OK rtt=0ms`.

## Decisions

- **A nominal lib, and no public API.** §2 gives `cli/` no public
  API, and the dependency chain of §2 puts it where nothing below
  can import it. `CliHarness.lean` declares nothing. The Lake lib
  `CliHarness` exists so the suite can import `Interop` and the
  gossipsub modules. Its roots are `CliHarness`, `Demo`, `PingNode`,
  `Interop`, `GossipsubInterop`, and `GossipsubSession`.
- **The go-side helpers stay scripts, test-only.** CLAUDE.md's
  dependencies rule keeps Go and Rust tooling test-only, confined to
  the harness, and never on a shipped or proof path. The tree holds
  `interop-matrix.sh` and `interop-slowreader/` under the root
  `scripts/`, beside the W0.3 vector tooling (§7 row 11's note).
  The ping checks are `scripts/ping-go/` and
  `scripts/ping-go-interop.sh`. `ping-go <multiaddr>` dials
  `pingnode serve`. `ping-go listen` serves `pingnode dial`.
  The module requires go-libp2p v0.50.0. The host Go toolchain builds
  the helper with `CGO_ENABLED=0`. That module asks for Go 1.26. The
  helper runs on the host loopback.
  This branch selects a contributor working decision for shutdown.
  The review context is
  https://github.com/etheorem/leanp2p/issues/22#issuecomment-6807493655.
  Noise, yamux, the host, and the CLI keep their fault propagation.
  An abrupt Go close still uses TCP RST (linger 0). A TCP read of
  that RST answers EOF, and the Noise session ends. A later write
  throws `closedError` in `Libp2p/Security/Transport.lean`:
  `resourceVanished` code 0, `noise: the secure connection is closed`.
  Yamux records the write. The session ended because the connection
  ended, so `Session.join` throws the write
  (`packages/net/yamux/docs/ARCHITECTURE.md`). `Host.close` throws
  that fault, and `guarding` returns 1. A nonzero
  `resourceVanished` code stays a fault. Commit
  `416bc8e33bd99502799ae3a924f34188ee9a8246` is the abrupt-close
  reproducer. Its three runs were exit 0
  (`PASS go-to-lean PING OK rtt=532.916µs`), exit 0
  (`PASS go-to-lean PING OK rtt=778.708µs`), and exit 1 with
  `stream failed: closed: the stream closed` and
  `resource vanished (error code: 0, noise: the secure connection is closed)`.
  The coordinated check keeps the Go host up after the ping. The
  helper cancels `ping.Ping`, reads the result channel until it
  closes, prints the result, and waits for stdin EOF. The driver
  reads `ADDR`, starts Go, requires `PING OK` while Go stays alive,
  closes the server stdin, requires server exit 0, closes the Go
  stdin, and requires Go exit 0. Three runs of
  `scripts/ping-go-interop.sh` with `LEAN_NUM_THREADS=1` exited 0 and
  printed `PASS go-to-lean PING OK rtt=834.084µs`,
  `PASS go-to-lean PING OK rtt=549.5µs`, and
  `PASS go-to-lean PING OK rtt=669.667µs`. Each stderr was empty.
  `finish_child` sends SIGTERM, waits at most 2 seconds, sends
  SIGKILL, and reaps the child. The owned children are the Go
  process, the Go stdin holder, the server stdin holder, and the
  server. The trap keeps the original status. A child that has
  already exited is reaped. `PING_GO_BIN=/usr/bin/false` exited 1
  with `FAIL go-to-lean: go exit 1`. A test-only peer that ignores
  SIGTERM exited 1 after 28.3 seconds, including its build, with
  `FAIL go-to-lean: go ping missed 25 s`. The cleanup bound on that
  miss is 33 seconds: the 25 second ping deadline, then 2 seconds
  for each of the four children. Those processes were gone after
  each check. The Go module pin and the Lean toolchain stay as they
  are. `ping-go listen` binds `/ip4/127.0.0.1/tcp/0` with TCP, Noise,
  and yamux, and enables the host ping service. It prints
  `ADDR <multiaddr> <peerid>` for the bound address, waits for stdin
  EOF, and then closes the host. `scripts/ping-go-interop.sh lean-to-go`
  runs `pingnode dial` with `LEAN_NUM_THREADS=1`, requires `PING OK`
  and dialer exit 0, then closes the Go stdin and requires Go exit 0.
  The owned children are the Go process, the Go stdin holder, and the
  dialer. Three runs exited 0 and printed `PASS lean-to-go PING OK
  rtt=1ms`, `PASS lean-to-go PING OK rtt=0ms`, and `PASS lean-to-go
  PING OK rtt=1ms`. `scripts/ping-go-interop.sh` with no argument
  printed `PASS go-to-lean PING OK rtt=973.708µs`.
  `PING_LEAN_BIN=/usr/bin/false scripts/ping-go-interop.sh lean-to-go`
  exited 1 with `FAIL lean-to-go: lean exit 1`. A test-only dialer
  that ignores SIGTERM exited 1 after 29 seconds, including its
  build, with `FAIL lean-to-go: lean ping missed 25 s`. Those
  processes were gone after each check. The reviewer independently
  confirmed both ping directions, the false dialer failure, and the
  stalled dialer. That stalled run failed after 28.3 seconds, and
  every tracked child was reaped. The confirmation is separate from
  the 29 second run above. The cleanup bound on that
  miss is 31 seconds: the 25 second ping deadline, then 2 seconds
  for the dialer, the Go process, and the Go stdin holder.
  `gofmt -l scripts/ping-go/main.go` printed nothing. `CGO_ENABLED=0
  go build` from `scripts/ping-go` completed. `bash -n
  scripts/ping-go-interop.sh` completed. Lean sources are unchanged
  in this slice, so the 138-check result above stands. That slice
  left the demo executable unfinished. The bidirectional gate stays
  unfinished. Echo support is `Libp2p.Protocols.TestSupport.Echo`.
  The demo command is the Demo lifetime section. The
  spike also kept a
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
  The pin is tag `v4.34.0`, commit
  `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`. The modules section
  records the consumer that compiled that commit and the rename to
  `CliHarness`. The hand-rolled parser remains the recorded fallback
  if a later pin fails v4.34, and the argument behavior above is the
  same on either route. The coordination client is in-repo Lean, as the spike's
  is, with no Redis client package.
- No build glue. The executables build through the declarative
  package metadata (PRINCIPLES 4.2).
