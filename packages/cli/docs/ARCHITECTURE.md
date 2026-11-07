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
| `CliApp.lean` | nominal build root, with no exported library API |
| `Main.lean` | the demo node, the `demo` executable; the §3.1 assembly as running code, the spike's `Main.lean` mapped here |
| `PingNode.lean` | the ping node, the `pingnode` executable; the `serve` and `dial` modes and their argument parsing |
| `CliApp/Demo.lean` | the demo's composition and workflow, exercised by `Tests/Cli.lean` |
| `CliApp/PingNode.lean` | the ping node's parser, server and client workflows, and stdin lifecycle |
| `CliApp/Mock/Stack.lean` | opaque interfaces for unmerged dependencies, with explicit failure bodies |
| `Interop.lean` (planned W5.9) | the transport-interop harness, the `interop` executable; the config environment and the listener and dialer modes |
| `Interop/Redis.lean` (planned W5.9) | the harness coordination client, private to the `interop` executable; the spike's `LeanP2P/Interop/Redis.lean` mapped here |

The package is executables only, with no exported library API (see
Decisions). The W0.1 scaffold gives every leaf a nominal `lean_lib`.
Its build root is `CliApp.lean`, which exports nothing. The executable
launchers import their own application module. The parser dependency
owns the module `Cli`, so retaining that scaffold name would collide
with the dependency. The import lint recognizes both roots as CLI.
Config parsing lives in each binary, because the three
contracts differ. Argument parsing uses `leanprover/lean4-cli` as
the first choice. The library is maintained under the leanprover
organization, and CLAUDE.md's "Lean on Lean" principle prefers a
maintained library before a hand-rolled one. The pin is
`e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` (`v4.34.0`), matching
the toolchain. The §2 rule bans
reusable code inside `cli/`; the parsing mechanism lives in the
dependency, and each binary keeps its own parsing code. The
hand-rolled parser is the recorded fallback if the pin does not fit
the v4.34 toolchain. The harness's go-side helpers are scripts
under the root `scripts/`, test-only per CLAUDE.md's dependencies
rule.

## Public surface

There is no library API, by design: every module here serves `main`
alone, and no consumer has anything to import (§2). The surface is the
three CLI contracts.

- **`demo`** (the spike's `Main.lean`). The spike demo takes no
  arguments. It listens on `/ip4/127.0.0.1/tcp/0`, generates two fresh
  Ed25519 identities, registers the ping and identify handlers and the
  echo demo handler, dials by peer id, pings, identifies, echoes, and
  closes both hosts. Whether W5.8 adds a listen-address flag, a dial
  target, or an identity key file is the unit's to fix.
- **`pingnode`** (the spike's `PingNode.lean`).
  `pingnode serve <port>` hosts `127.0.0.1:<port>`, serves
  `/ipfs/ping/1.0.0` and identify, as the spike's node does, prints
  `ADDR <multiaddr> <peerid>`, and exits when stdin closes.
  `pingnode dial <multiaddr>` dials an address whose `/p2p/<id>`
  suffix supplies the expected identity (the host pair's rule),
  pings once, and prints `PING OK rtt=<ms>ms`. A usage error exits 2.
  The final parsed component must be `p2p`, so a Unix path containing
  the text `/p2p/` cannot supply a peer identity. Ports contain only
  ASCII decimal digits and fit a `UInt16`; port zero requests an
  ephemeral listener. Extra arguments and unknown flags are errors.
- **`interop`** (the spike's `Interop.lean`). Configuration arrives as
  environment variables, in the shape of the libp2p
  transport-interop test plan: `transport` (`tcp`), `muxer` (`yamux`
  or `mplex`), `security` (`noise`), `is_dialer`, `ip`, `redis_addr`,
  and `test_timeout_seconds`. The listener publishes its dialable
  multiaddr with the `/p2p/<id>` suffix through Redis, and the dialer
  fetches it, dials, pings once, and prints the timing JSON with the
  test plan's keys verbatim, `handshakePlusOneRTTMillis` and
  `pingRTTMilllis`, typo included, because the runner compares the
  JSON keys literally. Diagnostics go to stderr, and
  a failure or a timeout exits nonzero.

## Owned contracts and how the package keeps them

1. **No protocol logic.** Every handler value and every client
   function comes from `libp2p/protocols`: ping and identify from that
   pair's surface, and the echo demo handler from its test support, as
   that pair records. Every seam value comes from its implementation
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
   package's error inductive.
4. **The ordered lists are assembled here and nowhere below** (§3.1).
   No code below `cli/` hard-codes which transport or muxer exists,
   and the demo's lists are the running statement of the composition.
5. **Every exit closes and joins.** Each mode closes the host before it
   returns, so the shutdown order of §5.5 joins every task the binary
   owns.
   The demo uses nested finalizers, so a failed second allocation
   still closes the first host. Each client stream resets after its
   exchange, including protocol errors and IO faults. Serve flushes
   its readiness line before waiting for stdin EOF. Its blocking
   stdin reader runs on a dedicated thread, and the async workflow
   parks on the reader's completion.
6. **The RESP2 reader is capped before allocation** (§5.1,
   PRINCIPLES 2.3). The Redis client reads server-supplied line and
   bulk lengths, each read is capped, and an over-long length is an
   error. The spike's client read `readExactly n` with no cap; the
   port adds the cap.

## Decisions

- **Executables only, with a nominal build root.** §2 gives `cli/`
  no public library API. `CliApp` lets Lake resolve the executable
  modules and exports nothing. Protocol behavior stays in the
  library packages below it.
- **The go-side helpers stay scripts, test-only.** CLAUDE.md's
  dependencies rule keeps Go and Rust tooling test-only, confined to
  the harness, and never on a shipped or proof path. The scripts are
  `pingd.go`, `interopd.go`, `ping-interop.sh`, and
  `interop-matrix.sh` under the root `scripts/`, beside the W0.3
  vector tooling (§7 row 11's note). The spike also kept a
  test-plans runner image, `interop/leanp2p/{Makefile,Dockerfile}`.
  The target drops the image, and `scripts/interop-matrix.sh` is the
  gate's only form, so docker appears only inside the scripts.
- **The demo composition doubles as the composition documentation**
  (root §2: "shows, as running code, how to compose the stack"). A
  reader who wants to compose the stack reads `CliApp/Demo.lean`;
  `Main.lean` is its executable entry point.

## What the package must not depend on

- Everything below is allowed, because §2 puts `cli/` at the left end
  of the chain. The rule that binds is the reverse: nothing below may
  import it, and no module in it may hold logic that a library wants.
- One new external dependency, `leanprover/lean4-cli`, for argument
  parsing. CLAUDE.md's dependency rule records it: the require block,
  `lake update`, the pinned rev, and `lake-manifest.json` committed.
  The hand-rolled parser is the recorded fallback if the pin does not
  fit v4.34. The coordination client is in-repo Lean, as the spike's
  is, with no Redis client package.
- No build glue. The executables build through the declarative
  package metadata (PRINCIPLES 4.2).

## Working ahead of dependencies

The current hackathon base has no concrete identity, host, security,
muxer-value or protocol implementation. The TCP unit is also open.
`CliApp.Mock` holds the dependency interfaces. The opaque operation
bodies fail explicitly; default commands cannot announce a bound
address or successful ping. No mock axiom is assumed.

`Tests.Cli` injects per-run host and protocol test values into each
executable's `Runtime`. It checks orchestration, not protocol bytes or
cryptography. Its records are local to a test; there is no mutable
global test mode. The application modules share no workflow helper.

The host docs freeze the required operations but leave their concrete
signatures to W5.6. `Mock.Host` expresses the CLI-side view: creation
from ordered configuration, listening with the actual bound address,
peerstore insertion, dial and dial-by-peer, negotiated stream opening,
handler registration, and an async close that joins owned work. The
host owner must confirm or adapt this view when W5.6 lands. This does
not add a real host implementation to the CLI.

The ping and identify adapters expose only the results printed by
these executables. At substitution, they call the actual protocol
clients and map their errors into `Host.Error`. The demo echo client
and handler must come from the protocol package's test support. They
are explicit pending connections, not implemented protocol logic in
this package.
