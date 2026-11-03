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
| `Streams/Error.lean` | `Streams.Error`, the error inductive of the package (§3.5): why a `Stream` operation did not complete |
| `Streams/Conn.lean` | `Connection`, `Listener`, and the `Transport` seam; `readExactly`; `withinUnauthDeadline`, the §5.4 deadline over a connection |
| `Streams/BufReader.lean` | `BufReader`, exact-length reads with a buffer over one connection, with the theorems of its offset arithmetic |
| `Streams/Framing.lean` | `Framing`, length-prefix reads: the `Prefix` shapes, the `Frame` codec with its `LawfulCodec` proof, the `ByteArray` path, and the IO read; the caps of §5.1 apply before allocation |
| `Streams/Stream.lean` | `Stream`, the application view over a muxer loop, with `prependBytes`; `Completions`, the tag table, as a pure state with its theorems; `LoopPort`, what a muxer shell gives one stream |
| `Streams/Tcp.lean` | the TCP transport, the production `Transport` value, over `Std.Async.TCP` (§9, delta 7); the mapping between a multiaddr and a socket address. Unit 1 makes it a stub whose `dial` and `listen` throw, and unit 2 gives it the sockets |
| `Streams/Sim.lean` | the in-memory sim, the test `Transport` value, with the dial/listen/echo harness and the byte-splitting hostile mode |
| `Streams/Mock/Bytes.lean` | the mock of `base/bytes` until W1.2 merges (see "The mocks") |
| `Streams/Mock/Varint.lean` | the mock of `codec/varint` until W2.1 merges, with two mock axioms |
| `Streams/Mock/Multiaddr.lean` | the mock of the multiaddr surface of `codec/multiformats` until W2.3 merges |

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
  reads until exactly `n` bytes arrive, and returns `none` on EOF. It
  also answers the bytes that it read past `n`, so no byte strands
  inside the call.
- `Listener` holds `addr`, `accept`, `close`, and `join`. `accept`
  returns `none` when the listener closes, so a parked accept wakes
  and ends. `join` is the completion of §3.1.
- `Transport` is the seam (§3.1) with `handles`, `dial`, and `listen`.
  It has no `id` field. The address picks the transport before any
  negotiation runs, so multistream-select never negotiates it. A
  multiaddr names its own protocol stack
  (`vendor/specs/addressing/README.md`, "multiaddr basics" and
  "Transport multiaddrs"). `handles` is how the address picks: it
  answers from the shape of the address alone. A consumer with more
  than one transport (§3.1, the ordered lists) dials and listens
  through the first one that handles the address. TCP handles the
  shapes that its socket mapping takes, `/ip4/…/tcp/…` and
  `/ip6/…/tcp/…`. The sim replaces the whole network of a test, so it
  handles every address. `dial` and `listen` throw a fault
  for an address that `handles` refuses. `dial` answers `none` when
  nothing listens at the address. Every other failure is a fault. The
  lifecycle is part of the seam (§3.1): `Connection.close` and
  `Listener.close` expose `close : IO Unit`, and the listener exposes
  a completion that the owner can join. The two values are the sim
  and TCP.
- `BufReader` serves one stage (§5.6). Two stages never share one
  reader. A reader is a value with no `IO.Ref`. Each read returns the
  bytes and the reader that holds the rest. `leftover` gives the bytes
  that a stage read too far, and `BufReader.new conn leftover` gives
  them to the next stage. So the types show the hand-over (§4.7).
- `Framing` reads a length prefix and then exactly that many bytes.
  Two prefix shapes exist, `uvarint` and `u16be` (the Noise frame). A
  read takes its cap with it, and the cap applies before any payload
  read (§5.1). A short prefix reports `truncated`, and a length over
  the cap reports `malformed`, both through the shared `DecodeError`
  of `base/bytes` (§3.2, §5.2). The framing core is proved over the
  byte model (§6): `Frame p cap` is a proof-carrying newtype with a
  `LawfulCodec` instance. The round-trip harness of `base/bytes` pins
  the `ByteArray` path to it. On the IO path, a connection that closes
  inside a frame ends the read as `none`, the end-of-stream channel of
  §3.5. The IO path never reports `truncated` for bytes that can no
  longer arrive.

  > **Note.** go-libp2p reports an error when the connection ends
  > inside a frame. It reads with `io.ReadFull`, which answers
  > `io.ErrUnexpectedEOF` (`vendor/go-libp2p/p2p/security/noise/rw.go`,
  > lines 130 and 144). Both answers close the connection. They differ
  > in what the owner learns.
- `Stream` is the application view over the loop of a muxer (§3.3).
  `read` takes from the `Chan` of the stream that the loop fills. The
  muxer bounds it, by a capacity or by its flow control. A reset reads
  as `.error .reset`, never as EOF (§5.2). After a chunk, `read` posts
  the count of its bytes (`LoopPort.postConsumed`), so a muxer with
  flow control returns the credit. `write`, `close`, and `reset` post
  `Event`s. The shell matches the answers to the writes by tag. The
  loop answers `Event.write sid tag bytes` with `Action.done tag` or
  `Action.refused tag e`. `Stream.write` waits on the slot of its tag.
  No promise enters a core.
- `Completions α` is the tag table of one session, generic in the
  answer. The writes share one table with `Unit` answers. A muxer can
  keep another table, such as one for the opens of streams, with the
  `Stream` as the answer.
- `LoopPort` holds what the muxer shell gives one stream: the inbox,
  the write table, and the closures that post its events.
  `LoopPort.endedBy` lets a muxer answer a reset that came after the
  inbox closed at the close of the peer. `Stream.ofPort` builds the
  stream, so each muxer writes the tag matching once, here.
- `prependBytes` puts the negotiation bytes that a stage read too far
  at the front of the stream.

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
- **The slot of a write is a `Chan` with one place.** The answer slot
  of a tag takes one value and then closes. A close wakes every park
  (PRINCIPLES 3.1). So when the loop ends, `Completions.closeAll` wakes
  every parked writer with `.error .closed`. An `IO.Promise` would need
  a second wake path for the end of the loop, and the `Std` await that
  `conc` wraps.
- **The tag table is a pure state.** `Completions.State` changes by
  three pure steps, `register`, `resolve`, and `closeAll`, and the
  shell applies each step in one `OnceRef.updateGet` (§4.1, rule 3).
  So its rules are theorems over the steps:
  - A tag is fresh when the table gives it.
  - An answer retires its tag, so a slot takes one answer at most.
  - A closed table gives no tag.
- **`BufReader` is a value.** A reader in an `IO.Ref` hides which stage
  owns the bytes in the buffer. A value that goes from read to read
  belongs to the stage that holds it. The hand-over to the next stage
  is then a function argument. The cost: a stage must not use an old
  reader value again, since it would read consumed bytes a second
  time.
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

## Theorems

The pure parts of the package carry theorems (§6, layer 1). The suite
in `Tests/Streams.lean` pins the IO parts.

- `Framing`: the `LawfulCodec` instance of `Frame p cap`, the round
  trip of each prefix shape (`decodeLength?EncodeLength`,
  `encodeLengthOfDecodeLength?`), the `truncated` answer of a short
  input (`decodeLength?U16beShort`, `Frame.decode?ShortPayload`),
  and the cap rule of §5.1 on the model (`Frame.decode?OverCap`) and
  on the IO path
  (`headerB?LeCap`, `headerB?OverCap`). `read` allocates its
  payload from the length that `headerB?` passed, so
  `headerB?LeCap` bounds the allocation by the cap.
- `take?`, the payload step: a take of the bytes in front of any rest
  returns them whole (`take?Append`), a successful take splits the
  input (`ofTake?`), and a short input is `truncated` (`take?Short`).
- `BufReader`: a new reader holds its seed, `drop` consumes what it
  names and no more, two drops act as one, and `peek` copies at most
  what it names.
- `Completions.State`: the rules of the decision above, with the
  freshness invariant kept by every step.
- `Tcp`: a port survives the trip through its two bytes
  (`be16Bytes16`), and the 16 bytes of an IPv6 value survive the trip
  through their 8 segments (`segments?FlatMapBytes16`).

## The mocks

W1.2, W2.1, and W2.3 are still open, so the package builds against
mocks of their frozen surfaces (RULES.md, "Working ahead of the tree").
Each mock lives in `Streams/Mock/` under the `Streams.Mock` namespace,
and imports nothing from the real package.

- A function of a mock is `opaque`, with a body. The compiler runs the
  body, so the suite runs real bytes. The kernel cannot unfold an
  `opaque` constant, so no proof can depend on the body.
- A type, a class, or a structure is a copy of the frozen shape. An
  `opaque` type has no constructors, and a pattern match on
  `Multiaddr.components` needs them.
- §4.2 freezes "the generic round-trip harness" and no names. So the
  harness of the bytes mock, `checkRoundTrips` and `checkModelPins`,
  and the field names of `LawfulCodec` follow the open W1.2 pull
  request, etheorem/leanp2p#30. The suite calls them in the same way
  before and after the swap.
- The varint mock states two axioms, `decodeEncodeSuffix` and
  `encodeDecode`. Each one is a theorem of W2.1, with the same name and
  statement (etheorem/leanp2p#34). They are the only axioms of the
  package beyond the three standard axioms of Lean.
- The multiaddr mock knows four protocols: `ip4`, `ip6`, `tcp`, and
  `memory`. The sim and the TCP stub use these four alone.

When a unit merges, the package deletes its mock and changes each
`open` of the mock namespace to the real one. The suite checks the
varint mock against the spec examples
(`Tests/vectors/varint-examples.json`) and the multiaddr mock on its
four forms, so a mock that drifts from the real surface fails before
the swap.

## Checked against the implementations

- **The transport answers for the address.** In go-libp2p, the
  transport itself says whether it serves an address, and the caller
  picks the transport by that answer. `Transport.CanDial` is the
  question (`vendor/go-libp2p/core/transport/transport.go`, line 69).
  The swarm drops a trailing `/p2p` component, then returns the first
  transport whose `CanDial` answers true
  (`vendor/go-libp2p/p2p/net/swarm/swarm_transport.go`, lines 37 to
  48). `handles` is the same question, so the types of `dial` and
  `listen` stay as they are.

## What the package must not depend on

- Nothing above `net`: no `libp2p`, no `cli` (§2).
- It is the bottom of the `net` group. `net/yamux` imports it, and the
  import never runs the other way (§2).
- The chain also allows `crypto`, `codec`, and `base` (§2). The
  package uses `codec/multiformats` for `Multiaddr` (dial, listen,
  and the connection addresses), `codec/varint` for the `uvarint`
  prefix of `Framing`, and `base`: `Async`, `Chan`, `select`,
  `TaskSet`, `OnceRef`, `withinDeadline`, and the `Clock` from
  `base/conc`, and the byte model and `DecodeError` from `base/bytes`.
  It uses nothing from `crypto`. Until W1.2, W2.1, and W2.3 merge, the
  mocks of "The mocks" replace those three packages.
- No protocol knowledge: no multistream message, no Noise frame, no
  yamux header. `Framing` knows the length-prefix shape alone, and the
  protocol layers own their message forms.
