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
| `Main.lean` | the demo node, the `demo` executable; the §3.1 assembly as running code, the spike's `Main.lean` mapped here |
| `PingNode.lean` | the ping node, the `pingnode` executable; the `serve` and `dial` modes and their argument parsing |
| `Interop.lean` | the transport-interop harness; the host assembly and the listener and dialer modes |
| `Interop/Main.lean` | the `interop` executable's `main`, apart from `Interop.lean` so the suite can import the harness |
| `Interop/Config.lean` | the test plan's environment variables, read into a `Config`, and the timing record |
| `Interop/Resp.lean` | RESP2, pure: the reply header parse with its caps, and the command encoding |
| `Interop/Redis.lean` | the harness coordination client, private to the `interop` executable: `PING`, `RPUSH`, and `BLPOP` over one connection; the spike's `LeanP2P/Interop/Redis.lean` mapped here |
| `Interop/Mock/Stack.lean` | the mock of the unmerged stack under the harness (RULES.md, "Working ahead of the tree"), until W5.2 to W5.7 merge |

The package is executables only, with no library root (see
Decisions). The W0.1 scaffold gives every leaf a nominal `lean_lib`;
the `cli` root stays empty, and the executables are the package.
Config parsing lives in each binary, because the three
contracts differ. Argument parsing uses `leanprover/lean4-cli` as
the first choice. The library is maintained under the leanprover
organization, and CLAUDE.md's "Lean on Lean" principle prefers a
maintained library before a hand-rolled one. The §2 rule bans
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
  a failure or a timeout exits nonzero. `ip` and `redis_addr` take
  literal IPv4 addresses (see Decisions).

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

## Decisions

- **Executables only, with no library root.** §2 gives `cli/` no
  public API, and the dependency chain of §2 puts it where nothing can
  import it. A root module would exist for re-export, and the only
  thing to re-export is `main`.
- **The go-side helpers stay scripts, test-only.** CLAUDE.md's
  dependencies rule keeps Go and Rust tooling test-only, confined to
  the harness, and never on a shipped or proof path. The scripts are
  `pingd.go`, `ping-interop.sh`, `interop-matrix.sh`, and
  `interop-slowreader/` under the root `scripts/`, beside the W0.3
  vector tooling (§7 row 11's note). The spike also kept a
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
  reader who wants to compose the stack reads `Main.lean`.

## The mock

W5.2, W5.3, W5.4, W5.6, and W5.7 are open, so the harness builds
against `Interop/Mock/Stack.lean`, a mock of their frozen surfaces
(RULES.md, "Working ahead of the tree"). A type is a copy of the frozen
shape, reduced to the fields the harness touches. An operation is
`opaque`, and its body fails with the name of the missing package: no
body fakes a connection or a handshake. The mock states no axiom.
W5.1 has merged, so the identity key and the peer id come from the
real `Libp2p.Identity`, and the harness generates its key through it.
Until the integration, a live run stops at the first host call, and
the gate cannot pass. At the integration, `Interop.lean` imports the
real packages, and the module goes.

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
