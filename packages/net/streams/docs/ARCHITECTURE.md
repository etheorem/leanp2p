# leanp2p streams: architecture

`net/streams` is the connection layer every higher package speaks
through. It holds the `Transport` seam with its two values, the
`Connection` and `Listener` types, the buffered and framed reads, and
the `Stream` seam that a muxer loop serves (§4.7). It has no libp2p
knowledge (§2). The package owns the TCP close
discipline and the no-reader-strand contract (§4.7), the framing caps
(§5.1), and the deadline wiring for the unauthenticated phases (§5.4).

## Modules

| Module | Holds, and why |
|---|---|
| `Streams.lean` | the root module; one import line per public submodule |
| `Streams/Constants.lean` | the constants this package owns, the 30 s deadline of §5.4 among them; one home per fact (§3.8) |
| `Streams/Conn.lean` | `Connection`, `Listener`, and the `Transport` seam; `readExactly` |
| `Streams/BufReader.lean` | `BufReader`, exact-length reads with a buffer over one connection |
| `Streams/Framing.lean` | `Framing`, length-prefix reads; the caps of §5.1 apply before allocation |
| `Streams/Stream.lean` | `Stream`, the application view over a muxer loop, with `prependBytes` |
| `Streams/Tcp.lean` | the TCP transport, the production `Transport` value, over `Std.Async.TCP` (§9, delta 7) |
| `Streams/Sim.lean` | the in-memory sim, the test `Transport` value, with the dial/listen/echo harness and the byte-splitting hostile mode |

All declarations live in the `Streams` namespace. The root module
re-exports the public submodules, including `Sim.lean` (§10, row 9), so
a suite imports one name. `Streams/Tcp.lean` is the only module that
touches `Std.Async.TCP` (§9, delta 7): a second transport or a
toolchain API change touches one module.

The spike modules `Net/{Transport,Tcp}.lean`,
`Conn/{Reader,Frame,Stream}.lean`, and `Sim.lean` are the reference
(§7 row 8; §10 rows 8-9). The spike's mutable sessions give way to the
core and loop of §3.3; the wire bytes and the tests carry over.

## Public surface

The names are §7 row 8's. The types follow §3.1.

- `Connection` holds `read`, `write`, `close`, `localAddr`, and
  `remoteAddr`. `read` returns `none` on EOF, the end-of-stream
  channel of §3.5; a fault is `IO.Error`. `readExactly` accumulates
  reads until exactly `n` bytes arrive, and returns `none` on EOF.
- `Listener` holds `addr`, `accept`, and `close`. `accept` returns
  `none` when the listener closes, so a parked accept wakes and ends.
- `Transport` is the seam (§3.1) with `dial` and `listen`, and with no
  `id` field: the address picks the transport before any negotiation
  runs, so multistream-select never negotiates it. The lifecycle is
  part of the seam (§3.1): `Connection.close` and `Listener.close`
  expose `close : IO Unit`, and the listener exposes a completion the
  owner can join. The two values are the sim and TCP.
- `BufReader` serves one stage (§5.6). Two stages never share one
  reader.
- `Framing` reads a length prefix and then exactly that many bytes. A
  read takes its cap with it, and the cap applies before any payload
  read (§5.1). A short prefix reports `truncated`, and a length over
  the cap reports `malformed`, both through the shared `DecodeError`
  of `base/bytes` (§3.2, §5.2). The framing core is proved over the
  byte model (§6), and the `ByteArray` path is pinned to it by the
  round-trip harness of `base/bytes`. On the IO path, a connection
  that closes mid-frame ends the read as `none`, the end-of-stream
  channel of §3.5; the IO path never reports `truncated` for bytes
  that can no longer arrive.
- `Stream` is the application view over the loop of a muxer (§3.3).
  `read` takes from the per-stream bounded `Chan` that the loop fills.
  `write`, `close`, and `reset` post `Event`s. The shell correlates
  completions by tag: the loop answers `Event.write sid tag bytes`
  with `Action.done tag` or `Action.refused tag e`, and `Stream.write`
  waits on the promise the tag maps to. No promise enters a core.
  `prependBytes` puts over-read negotiation bytes at the front of the
  stream.

## Owned contracts

1. **The TCP close discipline** (§4.7, verbatim): libuv drops
   cancelled promises, so `close` resolves the promise of the parked
   read itself. A double resolve is a no-op. `close` also sends a FIN
   to the peer. A failed write tears the connection down: the local
   read sees EOF, and the peer gets a FIN. The reason is PRINCIPLES
   3.1: never cancel; wake by close.
2. **No reader strand** (§4.7, verbatim): the stage that over-reads
   owns those bytes and hands them on as data. Every upgrade stage
   takes the leftover `ByteArray` of the previous stage and returns
   its own, so the types show the hand-over. The leftover goes to the
   layer that reads at the same level: ciphertext left after the Noise
   handshake seeds the reader of the Noise transport; plaintext left
   after the muxer negotiation is the first `Event` of the muxer loop;
   plaintext left after the protocol negotiation of a stream goes to
   the front of the stream (`Stream.prependBytes`). No two stages
   share a `BufReader`. With §5.6 this is one reader per physical
   stream.
3. **Every framing read is capped before allocation** (§5.1). The caps
   are multistream 1 KiB, mplex 1 MiB, yamux 256 KiB, Noise frame
   64 KiB, and Noise payload 8 KiB before authentication. `Framing`
   owns the shared shape, and each protocol layer passes its cap, from
   its own constants module or from a window it granted (PRINCIPLES
   2.3).
4. **Unauthenticated phases have a deadline** (§5.4): 30 s, wired
   through `withinDeadline` of `base/conc`. On expiry the deadline
   closes the connection, and the parked read ends on its own. The
   deadline covers only the unauthenticated phase; an authenticated
   connection that sits idle never expires.
5. **Every task has an owner that joins it** (PRINCIPLES 3.2). The
   accept loop and every per-connection task spawn into a `TaskSet`,
   and the owner joins them on close, in the order of §5.5: listeners
   first, then the pending connections.

## Decisions

- **The TCP transport binds `Std.Async.TCP` here and nowhere else**
  (§9, delta 7). The toolchain ships it over libuv in v4.34, and the
  wrapper module is the only file a toolchain move can break.
- **The sim is the second `Transport` value from the start** (§3.1).
  Every suite above the transport runs on it, and only the transport
  suite touches real TCP (PRINCIPLES 1.4). Its byte-splitting mode
  keeps write-boundary coupling visible; a sim that preserved write
  boundaries once hid a per-chunk cipher bug until TCP coalesced the
  bytes (PRINCIPLES 1.6). The listener registry changes through
  `OnceRef.update`, never get-then-set (PRINCIPLES 3.3).
- **`close` resolves the parked read's promise itself.** The runtime
  drops cancelled promises, so a cancel strands the waiter forever
  (PRINCIPLES 3.1). A resolve of an already-resolved promise is a
  no-op, so the close path and the read path can both resolve.
- **The deadline is the backstop over close-wakes.** Close wakes every
  park that shutdown knows about. A silent peer parks a dial that
  nobody closes, and the deadline closes it (PRINCIPLES 3.1; §5.4).
  The silent-peer incident hung shutdown this way in the spike.
- **Each cap has one home, in the package that owns it** (§3.8;
  PRINCIPLES 1.5). The protocol caps live in `Yamux.Constants`,
  `Noise.Constants` (`Libp2p/Security/Constants.lean`), and their
  siblings; `Streams/Constants.lean` holds
  only what this package owns. Two copies of a cap drift, and the peer
  sees the drift as a protocol error.

## What the package must not depend on

- Nothing above `net`: no `libp2p`, no `cli` (§2).
- It is the bottom of the `net` group. `net/yamux` imports it, and the
  import never runs the other way (§2).
- The chain also allows `crypto`, `codec`, and `base` (§2). The
  package uses `codec/multiformats` for `Multiaddr` (dial, listen,
  and the connection addresses), and `base`: `Chan`, `select`,
  `TaskSet`, `OnceRef`, `withinDeadline`, and the `Clock` from
  `base/conc`, and the byte model and `DecodeError` from `base/bytes`.
  It uses nothing from `crypto`.
- No protocol knowledge: no multistream message, no Noise frame, no
  yamux header. `Framing` knows the length-prefix shape alone, and the
  protocol layers own their message forms.
