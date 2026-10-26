# leanp2p yamux: architecture

`net/yamux` implements the hashicorp yamux spec over a `Connection` of
`net/streams` (§4.8). It holds the 12-byte header codec, the stream
state machine, and flow control. Yamux is the muxer the consensus
target requires (§8). The package has no libp2p knowledge (§2). The
libp2p `Muxer` value that assigns the `/yamux/1.0.0` id lives above, in
`libp2p/mux` (W5.4).

## Modules

| Module | Holds, and why |
|---|---|
| `Yamux.lean` | the root module; one import line per public submodule |
| `Yamux/Constants.lean` | the 256 KiB initial receive window, the frame-length cap, the control-queue cap, the inbound-stream backlog cap, and the 12-byte header size; one home per fact (§3.8) |
| `Yamux/Header.lean` | the `Header` type with the `Codec` and `LawfulCodec` instances (§3.2); the 12-byte layout is stated once, here |
| `Yamux/Sets.lean` | the closed sets of §3.4: `FrameType` and `GoAwayCode` with `toCode`/`ofCode?` and the round-trip theorem, and `Flags` as a `Bool` structure |
| `Yamux/Core.lean` | `State`, `Event`, `Action`, `ProtocolError`, the total `step`, and the invariant theorems |
| `Yamux/Loop.lean` | the loop task: the bounded `Chan Event`, the reader task, the action performance, and the tag-to-promise map |
| `Yamux/Session.lean` | the session entry over `Connection`; it serves `Stream` values |

All declarations live in the `Yamux` namespace, and the root module
re-exports the public submodules. The spike module `Conn/Yamux.lean`
is the reference (§7 row 9; §10 row 10), and `Tests/Yamux.lean` holds
the suite to carry over. Its session guards fields one by one and
takes a mutex per writer; §3.3 replaces that shape (§9, delta 8). Port
the tests and the wire bytes, and design the code from §3.3.

## Public surface

The names follow §3.1 and §3.3, derived from the spike session's
public functions (§7 row 9). The muxer entry itself moves to
`libp2p/mux` (W5.4).

- The session entry builds a `Session` over a `Connection`. The client
  and server roles pick the parity, and the plaintext the negotiation
  over-read arrives as a `ByteArray` handed in as data; the loop turns
  it into the first `Event` (§4.7).
- `openStream` opens a stream with a local id of our parity and sends
  the SYN. `acceptStream` returns the next inbound stream that the
  loop opened, as the spike's session does over its incoming channel.
- Stream traffic goes through the `Stream` seam of `net/streams`:
  `read`, `write`, `close`, and `reset`. The loop serves the seam, and
  the write completions arrive by tag (§3.3). A session-level ping and
  a `GoAway` go through the same event path, as the spike's `ping` and
  `goaway` do.
- `close : IO Unit` shuts the session down, and the owner joins the
  session completion (§3.1).
- The pure parts are the `Header` codec with its `LawfulCodec`
  instance, the closed sets, and `step`.

## The core

§3.3 fixes the shape, with the signature
`step : State → Event → Except ProtocolError (State × List Action)`.
`step` is total, and the loop that drives it is the one `partial def`
the package needs. `State`, `Event`, and `Action` are plain data: they
derive `Repr` and `BEq`, and they carry no `IO.Ref`, no `Task`, no
promise, and no function. `StreamId` is the proof-carrying newtype of
§3.7, and it carries the parity fact.

The `Event`s of this protocol: bytes arrived off the connection,
including the plaintext the muxer negotiation over-read (§4.7); the
application opened a stream; the application wrote to a stream, as
`Event.write sid tag bytes`; the application consumed n bytes of a
stream, as `Event.consumed sid n`; the application half-closed a
stream, or reset it; a tick. The `Action`s: write these bytes, one
frame; deliver these bytes to stream k; open stream k to the
application, paired with the ACK frame the spec requires for an
accepted stream; answer tag t, as `Action.done` or `Action.refused`;
close the connection.

The theorems cover the invariants of §3.3: the receive window never
goes negative, and stream ids keep their parity (client odd, server
even). The session-map theorem states the provable form: an entry
exists only while one of its directions is open, a retired id is never
reused, and unrequested streams stay within the backlog cap. Each
statement is about `step`, and `simp` and `omega` close it (§6).

## Owned contracts

1. **The receive window caps data frames** (§4.8, §5.1). The window we
   grant starts at 256 KiB (`Yamux/Constants.lean`). The core checks
   every data frame against it before the shell buffers a byte. Data
   beyond the window is a `ProtocolError` (§3.5); the session does not
   buffer it, and it tears the session down. The declared length is a
   32-bit field, and a reader that trusts it reads up to 4 GiB into
   memory (PRINCIPLES 2.3); the cap turns it into a bounded, checkable
   cost. On the send side, our writes stay inside the credit the peer
   granted. On the receive side, the application's reads become an
   `Event`, and the core answers with a window update that returns the
   credit to the peer.

2. **Only a SYN with the remote parity creates a stream** (§4.8). The
   client numbers odd and the server even, and 0 is reserved for the
   session; ping and GoAway ride on it, and no stream state exists at
   0. A SYN with our own parity is dropped. Frames for unknown ids are
   dropped; they create no state, and a later `openStream` of such an
   id still works.

3. **Streams retire once both sides have closed them** (§4.8). The
   core removes the entry when both directions are closed. With the
   backlog cap, this bounds the session map.

4. **A partially used credit grant hands the wake token on** (§4.8;
   PRINCIPLES 3.4). The shell counts the parked writers per stream and
   wakes one only while credit remains. A writer that used part of a
   grant leaves the rest to the next parked writer; a wake that stops
   at the first waiter is a lost wakeup.

5. **The control queue is capped** (§4.8; PRINCIPLES 3.4). ACK and
   ping-echo frames pass through a bounded queue. Beyond the cap the
   session drops the frames a peer can re-derive or re-request, so a
   hostile ping flood cannot grow the queue. The spike set the cap at
   1024; the number lives in `Yamux/Constants.lean`.

6. **Half-close follows the spec exactly** (§5.3; PRINCIPLES 2.2).
   Close ends the write direction of the closer. The read direction
   keeps working, and the response after our FIN still arrives. Reset
   aborts both directions.

7. **The session owns its tasks and names its closes** (§3.1;
   PRINCIPLES 3.1, 3.2). `close` closes the `Chan Event`, which wakes
   the loop. A stream reset closes the stream's credit channel, which
   wakes its parked writers. The loop and the reader spawn into one
   `TaskSet` that the owner joins. A `ProtocolError` reaches the owner
   through the session completion, never as a bare EOF (§3.5).

## Decisions

- **A pure core plus one loop task, against the spike's mutable
  session** (§3.3; §9, delta 8). The spike guarded fields one by one,
  took a mutex per writer, and grew a dedicated control-writer task
  when ACK writes raced handler writes. The core holds all of this
  state as data, and one loop task owns the core. Nothing inside a
  session spins or takes a lock, so `-N1` holds by construction.
- **Tags correlate write completions** (§3.3). The loop maps each tag
  to the promise that `Stream.write` waits on, so back-pressure stays
  exact and no promise enters the core.
- **Time is an `Event.tick` input** (§3.3). The spec fixes no timeout
  and no keepalive interval; the ping frame exists for keepalives, and
  a shell that schedules ticks owns the timing. The host owns the
  keepalive policy (§9, delta 2). A test replays a core that never
  reads a clock.
- **The header is a `LawfulCodec` with fixed-width fields** (§3.2).
  The layout is version (8 bits), type (8 bits), flags (16 bits),
  stream id (32 bits), and length (32 bits), all big-endian, 12 bytes
  in total. No field is a varint, so the codec runs over the `List
  Nat` model with plain byte arithmetic, and a prefix shorter than 12
  bytes reports `truncated` in the terms of the shared `DecodeError`.
- **The frame type and the `GoAway` code are closed sets** (§3.4).
  `FrameType` holds data, window update, ping, and `GoAway`.
  `GoAwayCode` holds normal termination, protocol error, and internal
  error. Each carries `toCode`/`ofCode?` and the round-trip theorem.
  `Flags` is the `Bool` structure `{ syn, ack, fin, rst : Bool }`, and
  the bit arithmetic happens once, in its `Codec` instance.
- **The inbound-stream backlog is capped** (the yamux spec,
  "Implementation considerations"). The spec's rule is a SHOULD: at
  most 256 streams a peer has opened and we have not acknowledged. The
  package caps all unrequested streams, accepted or not, which is
  stricter and is what bounds the session map together with the
  retirement rule.

## What the package must not depend on

- `net/streams` is the only import from its own group (§2, §7 row 9):
  the package reads and writes through `Connection` and serves the
  `Stream` seam.
- From `base`, what the loop needs: `Chan`, `TaskSet`, and `OnceRef`
  from `base/conc`, and the `Clock` if a shell schedules ticks. From
  `base/bytes`: the byte model, the shared `DecodeError`, and the
  `Codec` and `LawfulCodec` classes.
- Nothing from the `codec` group, and nothing from `crypto`. Every
  header field is fixed width, so the package needs no varint.
- No libp2p knowledge: no `ProtocolId`, no `Muxer` type, no
  multistream message. The `/yamux/1.0.0` id is named in `libp2p/mux`
  (W5.4), above the seam this package serves.
