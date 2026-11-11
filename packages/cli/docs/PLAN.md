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
| 1 | W5.7 | the demo node and the ping node binaries, with the composition wiring, as running code that documents it (root W5.8) | the root W5.8 row holds, the W5.8 behavior section of the package architecture holds, and the unit 1 milestones pass |
| 2 | 1 | the transport-interop harness, closed by its gate: the go-libp2p matrix `tcp + /noise + yamux`, dial and listen, plus the silent-peer and slow-reader scenarios (root W5.9) | the gate passes, and the unit 2 milestones pass |

Unit 0 is done.

## Consumers

None below. `cli/` is the end of the chain (§2), and nothing imports
it. The consensus client of §8 is the external consumer: it brings its
own node binary and uses only the libraries. The harness serves the
verification plan (§6, layer 6). The W6.4 gate is a later consumer of
the same pattern, a live run against foreign nodes.

## Test milestones (unit 1)

The executable roots are `Demo` and `PingNode`, in `packages/cli`.
`Main` stays the root of `gossipsub-interop`. The lib is
`CliHarness`. Its globs include `Demo` and `PingNode`, and the
lakefile names the `demo` and `pingnode` executables. A usage
error exits 2. `demo` prints `not implemented` and exits 1.
`pingnode serve` listens. `pingnode dial` dials the expected peer
and prints one ping.
The W5.8 behavior section
of the package architecture is the contract those binaries implement,
including the argument table, the exit codes, the ping and identify
deadlines, the
stream retirement, and the two-host close. Those deadlines start
after `newStream` returns. This branch selects two contributor
working decisions. The review context is
https://github.com/etheorem/leanp2p/issues/22#issuecomment-6805941244.
One-shot `pingnode dial` and `demo` apply a 30 second budget around
`Host.newStream`. Expiry fails the command and closes the owned
host. `pingnode dial` implements that timer. The demo echo handler
and client belong at `Libp2p.Protocols.TestSupport.Echo`. This slice
does not add that module. `pingnode serve` and `pingnode dial` are
implemented. `demo` still prints `not implemented`.

- The demo runs end to end over loopback: two hosts dial, complete the
  upgrade, identify, and exchange pings. The listener's identify
  record carries the bound address and the registered protocol ids.
  The echo leg joins this run when
  `Libp2p.Protocols.TestSupport.Echo` exists. Each `newStream` uses
  the exchange deadline after the call returns, and the 30 second
  budget around the call.
  The spike's node-suite legs are the carried tests (the spike's
  `Tests/Node.lean` drives two hosts over loopback TCP through ping,
  identify, and echo).
- `pingnode serve` prints the bound address, flushes it, and stays up
  until stdin EOF while an inbound dial still completes.
  `Tests/CliLive.lean` runs that check with `LEAN_NUM_THREADS=1`.
  The server reads stdin with `Handle.getLine` in `IO`, outside
  `Async`. The same file checks immediate EOF, a busy port, a failed
  `ADDR` write, an inbound failure followed by a live exchange, and
  a sleeper that misses its deadline, and a registered task that
  returns an error. Each of those process checks reaps the child and
  joins the readers it started. A task error from one of those joins
  fails the check after the remaining joins. The focused command
  `LEANP2P_SUITE=cli LEAN_NUM_THREADS=1 .lake/build/bin/tests +RTS -N1 -RTS`
  passed 121 checks, with 0 failed, 0 todo, and 0 skipped. That
  command runs the CLI suites alone. The full `lake test` was not
  rerun for this slice. Its recorded baseline still has one failure
  in `Tests/Streams.lean`: `the teardown aborted the stuck write:
  the peer meets a reset`.
  `scripts/park-threads.lean` measures `IO.wait`.
- A usage error exits 2 before a host exists: a `demo` argument, a
  missing or unknown `pingnode` subcommand, an extra operand, a port
  outside 0..65535, a multiaddr that fails `Multiaddr.parse?`, a
  dial address that `Host.splitPeer` rejects, and a dial address
  whose transport prefix still contains a `p2p` component. A line
  break in an operand stays inside that one stderr line.
  `Tests/Cli.lean` runs the built binaries for these cases. A valid
  `demo` list exits 1 with the unfinished diagnostic. A dial to
  port 0 uses `capture` with a 10 second deadline. The child exits
  inside that deadline with code 1, empty stdout, and a nonempty
  runtime diagnostic. A valid `pingnode serve` port reaches
  `startListening`.
- `pingnode dial` against `pingnode serve` prints `PING OK rtt=<ms>ms`
  and exits 0. The server then exits 0 on stdin EOF. The command
  passes the parsed address and the expected peer to `Host.dial`.
  `Host.newStream` runs under `Streams.unauthDeadlineMs`. Expiry
  closes the owned host and joins the open and the cleanup task.
  `release` resets a late stream. The exchange deadline starts after
  `newStream` returns, and expiry resets that stream. A protocol
  failure resets the stream and maps through `Ping.mapPingError`.
  `Tests/CliLive.lean` also covers a closed port, an expected-peer
  mismatch, a peer that stays silent during protocol selection, and
  a peer that reads the payload and writes no echo. Each failure
  before a successful ping has empty stdout. The capture bound on
  the two silent peers is 50 seconds, and the command exits inside
  it. The dial slice recorded `lake build demo pingnode tests`,
  then `LEANP2P_SUITE=cli .lake/build/bin/tests` and `LEANP2P_SUITE=cli
  LEAN_NUM_THREADS=1 .lake/build/bin/tests +RTS -N1 -RTS`. Each of
  those suite runs passed 137 checks, with 0 failed, 0 todo, and 0
  skipped. The port-zero correction builds with `lake build tests`.
  `LEANP2P_SUITE=cli LEAN_NUM_THREADS=1 .lake/build/bin/tests +RTS -N1
  -RTS` passed 138 checks, with 0 failed, 0 todo, and 0 skipped.
  That command runs the CLI suites alone. The added check is the
  bounded port-zero exit. `scripts/lint-imports.sh` checked 189
  module files, with 0 violations. `git diff --check` reported no
  whitespace errors. The 121-check command above is the serve
  slice. The full `lake test` was not rerun. Its recorded baseline
  still has one failure in `Tests/Streams.lean`: `the teardown
  aborted the stuck write: the peer meets a reset`. Lean-to-Go, the
  demo, echo, and the bidirectional gate remain unfinished.
- Go-to-Lean ping is in this slice. The Go peer dials `pingnode
  serve`. `scripts/ping-go/main.go` dials one multiaddr over TCP,
  Noise, and yamux, prints `PING OK rtt=<duration>`, and waits for
  stdin EOF before it closes the host. The module requires
  `github.com/libp2p/go-libp2p v0.50.0`. The host Go toolchain builds
  it with `CGO_ENABLED=0`. The module asks for Go 1.26.
  `scripts/ping-go-interop.sh` starts `pingnode serve 0` with
  `LEAN_NUM_THREADS=1`, joins the `ADDR` fields, and requires the
  ping line while Go stays alive. It then closes the server stdin,
  requires server exit 0, closes the Go stdin, and requires Go exit
  0. `finish_child` ends an owned child that misses its wait:
  SIGTERM, at most 2 seconds (`term_grace`), SIGKILL, then `wait`.
  The owned children are the Go process, the Go stdin holder, the
  server stdin holder, and the server. A child that has already
  exited is reaped. The trap keeps the script's status. The abrupt
  Go-first close remains the historical case in the architecture
  decision, at commit `416bc8e33bd99502799ae3a924f34188ee9a8246` and
  https://github.com/etheorem/leanp2p/issues/22#issuecomment-6807493655.
  That close can still surface the failed write. The library fault
  rules stay in place. Three coordinated runs exited 0 and printed
  `PASS go-to-lean PING OK rtt=834.084µs`,
  `PASS go-to-lean PING OK rtt=549.5µs`, and
  `PASS go-to-lean PING OK rtt=669.667µs`, each with empty stderr.
  `PING_GO_BIN=/usr/bin/false scripts/ping-go-interop.sh` exited 1
  with `FAIL go-to-lean: go exit 1`. A test-only peer that ignores
  SIGTERM, passed as `PING_GO_BIN`, made the script exit 1 after 28.3
  seconds, including its build, with
  `FAIL go-to-lean: go ping missed 25 s`. The Go process, both stdin
  holders, and the server were gone. The cleanup bound on that miss
  is 33 seconds: the 25 second ping deadline, then 2 seconds for
  each of the four children. The check stays outside `lake test`.
  Lean-to-Go, the demo, echo, and the bidirectional gate remain
  unfinished. The spike selected its muxer from the Noise handshake
  extension. This stack negotiates the muxer on the wire (the
  negotiate pair's decision).
- The in-suite legs pass under `+RTS -N1` (§6; PRINCIPLES 5.3).

## Test milestones (unit 2)

- The gate: the interop matrix against go-libp2p v0.50.0, over
  `tcp + /noise + yamux`, dial and listen, both directions, with the
  two harness executables coordinated through Redis in docker, per
  `scripts/interop-matrix.sh`. A cell passes when the dialer prints
  the timing JSON of the `interop` contract. The cells: go dials go
  (the check of the setup), Lean dials go, go dials Lean, and Lean
  dials Lean. The script writes the records and a results table in
  the test plan's `name,outcome` shape.
- The matrix cells for mplex are skipped against go v0.50, which
  removed mplex from its defaults (the mux pair's record).
  `scripts/mplex-interop.sh` runs `Mux.mplex` against go-mplex v0.7.0
  over loopback TCP, in both directions, and the mux suite covers the
  identity rule in-process.
- The silent-peer scenario, the carried regression (PRINCIPLES 5.4):
  a raw connection that sends nothing fails the upgrade at the
  deadline (§5.4), and teardown closes the pending connection and
  joins every task. The host pair carries the in-suite form; the gate
  runs it live against the composed binary: a raw TCP client connects
  to the Lean listener, holds its write side open, and sends nothing.
  The listener closes it no earlier than the 30 s deadline, and a go
  dialer passes against the same listener meanwhile.
- The slow-reader scenario: the spike ran no live leg for it. The
  in-process evidence is the yamux flow-control work, a transfer
  larger than the 256 KiB initial window completing in both directions
  over noise-encrypted TCP, and data beyond the receive window failing
  as a protocol error. The live leg (`scripts/interop-slowreader/`): a
  go peer dials the Lean listener, opens a ping stream, and writes
  32-byte payloads without reading the echoes. Lean's ping handler
  parks on its full send window and stops reading, so its receive
  window fills, and the go writes stall. The scenario passes when the
  writes stall below 64 MiB, the bound of §5.1's receive path with
  room for both windows and the kernel buffers, and a second ping over
  a fresh stream on the same connection completes.
- In the suite (`Tests/Interop.lean`): the configuration table and the
  timing record; the RESP2 header parse with both caps; the Redis
  client against a scripted server over the sim, with whole writes and
  in the byte-splitting mode; a reply line over the cap; the CRLF scan
  pinned to its model; and the published address.
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
