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
| `Yamux/Constants.lean` | the 256 KiB initial receive window, the window-update threshold, the send frame-length cap, the control-queue cap, the ACK backlog, the inbound-stream cap, the event-queue capacity, the write deadline, the ping deadline, the keepalive interval, the 12-byte header size, and the 32-bit id limit; one home per fact (§3.8) |
| `Yamux/Header.lean` | the `Header` type with the `Codec` and `LawfulCodec` instances (§3.2), and the `ByteArray` path (`encodeB`, `decodeAt?`); the 12-byte layout is stated once, here |
| `Yamux/Sets.lean` | the closed sets of §3.4: `FrameType` and `GoAwayCode` with `toCode`/`ofCode?` and the round-trip theorem, and `Flags` as a `Bool` structure with its `Codec` instance |
| `Yamux/Core.lean` | `Role`, `StreamId`, `StreamKey`, `State`, `Event`, `Action`, `ProtocolError`, and the total `step` |
| `Yamux/Invariants.lean` | the invariant theorems over `step`: the window, the inbox, no dropped byte, parity, retirement of ids and keys, and the inbound cap |
| `Yamux/Loop.lean` | the IO shell: the reader, loop, and writer tasks, the action performance, and the teardown |
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
  it into the first `Event` (§4.7). A `Clock` (default `Clock.system`)
  runs the timers, so a test can move the time. The host passes its
  keepalive interval (`keepalive`, go-yamux's 30 s by default, `none`
  for no keepalive).
- `openStream` opens a stream with a local id of our parity and sends
  the SYN. `acceptStream` returns the next inbound stream that the
  loop opened, as the spike's session does over its incoming channel.
- Stream traffic goes through the `Stream` seam of `net/streams`:
  `read`, `write`, `close`, and `reset`. The loop serves the seam, and
  the write completions arrive by tag (§3.3). A read posts the count of
  the bytes it took (`LoopPort.postConsumed`), and the core returns
  that credit to the peer. A session-level ping and a `GoAway` go
  through the same event path, as the spike's `ping` and `goaway` do.
- `close : IO Unit` shuts the session down, and the owner joins the
  session completion (§3.1): `join` answers `Except ProtocolError
  Unit`. A read fault of the connection throws, and so does a write
  past the write deadline, as `timeExpired`.
- The pure parts are the `Header` codec with its `LawfulCodec`
  instance, the closed sets, `StreamId`, and `step`.

## The core

§3.3 fixes the shape, with the signature
`step : State → Event → Except ProtocolError (State × List Action)`.
`step` is total, and the loop that drives it is the one `partial def`
the package needs. `State`, `Event`, and `Action` are plain data: they
derive `Repr` and `DecidableEq` (and so `BEq`), and they carry no
`IO.Ref`, no `Task`, no promise, and no function. Their bytes sit in
`Bytes.Blob`, the shared wrapper with a `Repr` instance, since §3.2
forbids one on `ByteArray`. `StreamId` is the proof-carrying newtype of §3.7: it
carries the opener, the parity fact, the nonzero fact, and the 32-bit
bound. The core checks a peer's id once, at the SYN
(`StreamId.ofRemote?`). An entry holds its `StreamId`, its epoch, and
a `StreamState`; the entry operations return a new `StreamState` only,
so no operation can change an id or an epoch.

The application names a stream by its `StreamKey`: the id and the
epoch. The session counts its streams, ours and the peer's, and each
new stream takes the next epoch. The peer may open an id again after
its stream retired ("How this package reads a root rule"), so the id
alone does not name a
stream: a `Stream` handle of the old stream would act on the new one.
The handle posts under its key, and an event under a key that no live
stream has changes nothing. go-yamux gets the same effect from its
handles, which are pointers.

The `Event`s of this protocol: bytes arrived off the connection,
including the plaintext the muxer negotiation over-read (§4.7); the
connection ended; a tick; the application opened a stream; the application
wrote to a stream, as `Event.write key tag bytes`; the application
consumed n bytes of a stream, as `Event.consumed key n`; the
application half-closed a stream, or reset it; the application pinged;
the application went away. The `Action`s: write this frame; write this
ping echo, or drop it at the cap; write this answer to a SYN, under
back-pressure; deliver these bytes to stream k;
end stream k's reads by EOF or by a reset; offer stream k to the
application, after the ACK frame the spec requires for an accepted
stream; answer an open with the stream or a refusal; answer tag t, as
`Action.done` or `Action.refused`; report a write that sent all the
credit there was (`Action.blocked`), that stream k has credit
(`Action.credit`), and that stream k's write direction ended
(`Action.endWrites`), so the shell parks and wakes its writers
(contracts 4 and 7); ask for a tick at the next deadline
(`Action.wakeAt`); end the session for a keepalive that no pong
answered (`Action.expired`); shut the session down. The ticks drive
the two session timers of go-yamux: the pong's deadline and the
keepalive (`Yamux/Core.lean`, "Time"). The actions
that start a stream (`opened`, `accept`) carry its key; the others
name the stream by its id, which is live while the action applies.

The theorems cover the invariants of §3.3 (`Yamux/Invariants.lean`).
The receive window never goes negative: every stream state carries
`recvWindow + unread ≤ initialWindow`, and `recvDataWindow` shows the
check behind it. The inbox is bounded: every stream state carries
`slots ≤ inboxChunks` and `inInbox + held ≤ unread`, and `stepInbox`
states that a stream buffers at most the window, in at most
`inboxChunks` chunks plus one held chunk. These two hold by
construction, for every state; they bound the core's count of the
inbox, and the suite tests that the shell's `Chan` follows the count.
No byte that the window charged is dropped: in every reachable state,
the bytes of the data frame still to come are charged to their stream
(`RxOk`, `Reachable.rxOk`), so `offer` keeps every chunk whole
(`offerKeeps`). Stream ids keep their parity (client odd, server
even): `StreamId` carries it, and `stepParity` states it after a
step. The session-map theorem states the provable form, as the
invariant `Inv` that every step keeps (`stepInv`, `Reachable.inv`):
an entry exists only while one of its directions is open (or bytes and
the EOF still wait for its reader), every id we opened is below our
counter, every epoch is below the epoch counter, and the streams the
peer opened stay within `maxIncomingStreams`. Our retired ids are never
reused: `stepRetired` states it, since our counter only grows. The
peer numbers its own streams, and it may open a retired id again
(go-yamux and rust-yamux do the same; "How this package reads a root
rule"). The key of a stream never comes back, ours or the peer's
(`stepRetiredKey`), and an event under a retired key changes nothing
(`stepStale`). "How this package reads a root rule" below says how
these theorems meet the root wording. Each proof
composes one lemma per table operation, and `simp` and `omega` close
the arithmetic (§6).

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

   > **Note.** Such a SYN, and a SYN on id 0, also ends the session
   > with a protocol-error go-away (`invalidStreamId`). "Checked against
   > the implementations" records the sides.

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

   > **Note.** go-yamux drops echoes past its own cap, and rust-yamux
   > stops reading instead ("Checked against the implementations").

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
- **Each write to the connection has a deadline.** A peer that
  stops reading parks the writer, and the loop waits for the writer
  under the back-pressure of contract 5, so without a bound one silent
  peer holds the session forever. The writer runs each write under
  `withinDeadline` on the session's `Clock`. At `writeDeadlineMs`,
  10 seconds, the expiry records a `timeExpired` fault and closes the
  connection: the parked write wakes, the reader sees the end, and
  `join` throws the fault. The source is go-yamux: each write of its
  send loop runs under `ConnectionWriteTimeout`, 10 seconds
  (`vendor/go-yamux/mux.go`, line 76; `session.go`, lines 581 to 587), and a failed
  write closes the session. Root §5.4 does not ask for it: its
  deadlines cover the unauthenticated phases.
- **One writer task, beside the loop, the reader, and the ticker**
  (§3.3). go-yamux runs its writes in a send loop of their own
  (`vendor/go-yamux/session.go`, line 161). The loop never parks on the
  connection: a frame goes to the writer's queue, bytes go to a free
  slot of a stream's inbox or to the core's held chunk, and an answer
  goes to a tag's slot. A loop
  that wrote to the connection itself could deadlock against a peer
  that does the same: each loop parked on a write, each reader parked
  on a full event queue. The writer is the one task that parks on the
  peer. It answers a write's tag after the frames before it have gone
  to the connection, so back-pressure stays exact. The writer's queue
  has no capacity limit: the writers bound the data, local operations
  bound their own frames, and the counter of contract 5 bounds the
  frames the peer causes. Under that back-pressure the loop parks on
  the writer's `room` signal as well as on the event queue
  (`Yamux/Loop.lean`, `run`). `Session.close` closes both, and the
  writer closes `room` when it ends, so the loop blocks only on
  channels its shutdown closes (root §3.3).
- **The reader reads one read ahead of the loop** (§3.3; §5.1). The
  bytes of a read count against no window until the core steps them,
  and the event queue alone would hold `eventQueueCap` reads of them:
  4 MiB of a connection. The reader takes a credit before each read,
  and the loop returns it after the step, so one read at most waits
  outside the windows. Over Noise, one read is one decrypted message,
  at most 65519 bytes. go-libp2p reads the same amount ahead: it runs
  go-yamux with no read buffer (`ReadBufSize = 0`, `vendor/go-libp2p`,
  `p2p/muxer/yamux/transport.go`, line 29), and its Noise session holds
  one decrypted message (`qbuf`, `p2p/security/noise/rw.go`, lines 39
  to 86).
- **The event queue holds 64 events** (§3.3). The spec fixes no
  number. With the reader's credit, the queue holds the operations of
  the application and one read at most, so the number decides only how
  many operations wait before their tasks park. go-yamux parks an
  application write on a send queue of 64 (`sendCh`,
  `vendor/go-yamux/session.go`, line 144; `sendMsg`, line 536).
- **The inbox is bounded, and the core holds the overflow** (§3.3). A
  stream's inbox is a `Chan` of `inboxChunks` data slots plus one slot
  for the reset or the end of the session. The core counts the slots
  it filled (`StreamState.slots`); a read frees one and posts its
  count. While the inbox is full, the core joins the arriving bytes
  into one held chunk (`StreamState.held`), and the next free slot
  takes it. The held bytes count as unread, so the window bounds them,
  and a peer FIN waits behind them (`eofDue`). A capacity of a whole
  window in chunks would be no answer: the `Std` channel allocates
  every slot up front. The 16 slots follow go-yamux, whose receive
  buffer allocates 16 segments up front, one per frame
  (`newSegmentedBuffer`, `vendor/go-yamux/util.go`, line 83). The join appends in
  place, so a window of 1-byte frames costs linear time; the suite
  holds that bound (`coreInboxChecks`).
- **The flush after the end can wait on the peer, for one write
  deadline.** The writer writes what its queue holds, the last go-away
  among it, and then closes the connection. A peer that stops reading
  parks it until the write deadline closes the connection. An owner
  that needs a shorter bound runs `join` under `withinDeadline` and
  closes the connection on expiry (PRINCIPLES 3.1; §5.4). go-yamux's
  close waits for its send loop the same way, for at most one
  `ConnectionWriteTimeout` (`vendor/go-yamux/session.go`, lines 313 to
  316).
- **A step that fails drops its event.** The signature of §3.3 makes
  `step` return the error alone, so the actions of the failing event
  never run, deliveries included. A protocol failure closes the
  connection (§3.5), so the session ends there, and every stream reads
  `closed`.
- **The faults of the connection reach `join`** (§3.5: a socket error
  is a fault). A read fault, a write past its deadline, and a keepalive
  that no pong answered throw from `join`. A failed write throws too,
  unless the peer's normal go-away or the owner's close ended the
  session. go-yamux's send loop closes the session with its write
  error, but prefers the receive loop's go-away
  (`vendor/go-yamux/session.go`, lines 545 to 566; the normal go-away
  is a `GoAwayError` too, `const.go`, line 120), and keeps the error
  only when the owner's `Close` has not set `shutdownErr` first (lines
  283 to 306). The two owners of a connection can close at once, and
  the peer's close can fail our write before our loop reads the
  go-away. A session that ends at the end of the connection still
  throws the failed write. After a failed
  write the writer stops writing and answers the remaining tags
  `closed`. The first end of the session wins: a fault after it is the
  end itself.
- **A flag bit outside the four is ignored.** The spec defines four
  flags and says nothing of the other bits; go-yamux and rust-yamux
  ignore them. `Flags.other` keeps them, so a decode re-encodes to its
  input under the `LawfulCodec` law, and the core reads the four flags
  alone.
- **The ACK goes out at once.** The spec allows a receiver to delay
  the ACK until the application takes the stream (the spec, line 170).
  This document pairs the offer of a stream with "the ACK frame the
  spec requires for an accepted stream" ("The core"), so the core
  sends it when it creates the stream, and the accept queue bounds the
  streams that wait for `acceptStream`. The accept queue holds `backlogCap`
  streams; a stream that finds it full (a reset stream the application
  has not taken still holds a place) is reset at once through the
  core. The core emits the ACK before the offer, so the wire then
  carries the ACK, then the RST: an accepted stream, then a reset,
  where RST before ACK on one id would break the spec's one answer to
  a SYN.
- **Our own opens wait beyond the ACK backlog.** The spec defines the
  ACK backlog as "the number of streams that a peer has opened which
  have not yet been acknowledged", and implementations "SHOULD at most
  allow an ACK backlog of 256 streams" (the spec, lines 164 to 167). So
  at most 256 of our streams wait for the peer's ACK. A further open
  waits in the state, in order, and an ACK lets it through. rust-yamux
  waits the same way (`MAX_ACK_BACKLOG`,
  `vendor/rust-yamux/yamux/src/connection.rs`, line 499), and go-yamux
  blocks its opener on a semaphore of `AcceptBacklog` places (`synCh`,
  `vendor/go-yamux/session.go`, lines 84 to 86 and 205 to 212).
- **A close refuses the parked writes.** No data may follow a FIN, so
  `close` closes the stream's credit channel, and the writers parked on
  it wake with `closed`. go-yamux's `CloseWrite` wakes its parked
  writers the same way, and they return `ErrStreamClosed`
  (`vendor/go-yamux/stream.go`, lines 158, 159, and 323). A writer that wrote and then closed has its
  answer already.
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

  > **Note.** `Flags` has one more field, `other`, for the twelve bits
  > the spec does not define, so that a decode re-encodes to its input
  > (`LawfulCodec`). The core ignores them ("Checked against the
  > implementations").
- **The inbound-stream backlog is capped** (the yamux spec,
  "Implementation considerations"). The spec's rule is a SHOULD: at
  most 256 streams a peer has opened and we have not acknowledged. The
  package caps all unrequested streams, accepted or not, which is
  stricter and is what bounds the session map together with the
  retirement rule.

  > **Note.** The cap is `maxIncomingStreams`, 256, the one number of
  > this decision ("Checked against the implementations" records the
  > references).

## Checked against the implementations

The spec leaves several answers open. Each behavior below was checked
against go-yamux v5.1.0 (`vendor/go-yamux`, the version go-libp2p
v0.50.0 requires, the interop target of W5.9) and rust-yamux 0.14.1
(`vendor/rust-yamux`); a cell cites a file of that copy. The last
column names the check in `Tests/Yamux.lean` that pins the package's
answer.

| Behavior | The spec | go-yamux | rust-yamux | This package |
|---|---|---|---|---|
| version other than 0, unknown type | version "always set to 0" | session error (`session.go`, lines 737 to 745) | session error (`yamux/src/frame/header.rs`, lines 369 to 380) | `malformedHeader` ("header: a version other than 0 is malformed") |
| flag bit outside the four | defines four flags | ignored (`const.go`, lines 217 to 219) | ignored (`yamux/src/frame/header.rs`, line 382) | ignored: `Flags.other` carries the bits through the codec ("header: a flag bit outside the four decodes, and the four flags read as sent") |
| SYN with our parity | client odd, server even | the session ends, with no go-away (`session.go`, lines 846 and 691 to 694) | the session ends with a protocol-error go-away (`yamux/src/connection.rs`, lines 619 to 621) | `invalidStreamId`: the session ends with a protocol-error go-away, as rust, since the spec says a go-away "should be sent" when a session ends ("Session termination") ("a SYN with the wrong parity draws a protocol-error go-away") |
| SYN on id 0 | "the 0 ID is reserved to represent the session" | parity alone (`session.go`, line 846) | parity alone (`yamux/src/connection.rs`, lines 887 to 895) | `invalidStreamId`, by the spec's reservation of id 0 ("a SYN on id 0 is invalidStreamId") |
| SYN for a live id | silent | protocol-error go-away (`session.go`, lines 869 to 877) | protocol-error go-away (`yamux/src/connection.rs`, lines 623 to 625) | `duplicateStream`, go-away ("a SYN for a live stream is an error") |
| SYN of the peer's parity for an id that is not live, in any order or again after it retired | client odd, server even; no order | opens a new stream (`session.go`, lines 869 to 877) | opens a new stream (`yamux/src/connection.rs`, lines 617 to 639) | opens a new stream with a new key; our own ids never come back (`stepRetired`) ("the peer may open one of its retired ids again") |
| a peer that stops reading | silent | `ConnectionWriteTimeout`, 10 s, then the session closes (`mux.go`, line 76; `session.go`, lines 581 to 587) | not checked | `writeDeadlineMs`, 10 s, then the session ends with `timeExpired` ("the parked write ends the session at the write deadline") |
| inbound streams | SHOULD cap the ACK backlog at 256 | `MaxIncomingStreams` 1000, then RST (`mux.go`, line 77; `session.go`, lines 879 to 885); go-libp2p lifts it, and its resource manager resets inbound streams past 256 per peer (`vendor/go-libp2p`, `p2p/muxer/yamux/transport.go`, line 32; `p2p/host/resource-manager/limit_defaults.go`, lines 813 to 833) | 512 streams, ours and the peer's, then a go-away for the whole session (`yamux/src/lib.rs`, line 90; `yamux/src/connection.rs`, lines 627 to 629) | 256 live inbound streams, then RST (`maxIncomingStreams`) ("a SYN beyond the inbound cap is refused with RST") |
| data beyond the window | the 256 KiB window | protocol-error go-away (`session.go`, lines 787 to 791) | protocol-error go-away (`yamux/src/connection.rs`, lines 663 to 671) | `windowExceeded`, go-away ("data beyond the window ends the session with the error") |
| data after the peer's FIN | FIN: "will send no further data" | no error; charged, buffered (`stream.go`, lines 469 to 485) | no error; charged, buffered (`yamux/src/connection.rs`, lines 660 to 680) | no error; charged, and readable ahead of the EOF while the EOF waits (`Entry.recvData`) ("data after the peer's FIN is no error") |
| frames for an unknown id | silent | drained (`session.go`, lines 769 to 777) | dropped (`yamux/src/connection.rs`, lines 681 to 695) | dropped; the payload passes by ("frames for an unknown id create no state") |
| window update | "sent regularly" | when half the window is free (`util.go`, lines 103 to 107) | not checked | when half the window is free ("consuming half the window sends a window update for it") |
| ACK of an inbound stream | MAY wait for the application | with the first write or read (`stream.go`, lines 206 to 208) | not checked | at once (decision above) ("a SYN with the peer's parity creates the stream, with the ACK") |
| RST with bytes the reader has not taken | "Reset a stream immediately" | the next read answers the reset, and the buffer goes unread (`stream.go`, lines 105 and 106) | the reads drain, then EOF (`yamux/src/connection/stream.rs`, lines 353 to 356) | the next read answers `.error .reset`; the shell drops the unread chunks and the core its held bytes (`Yamux/Loop.lean`, "The reset") ("an RST drops the unread bytes, and the read answers reset") |
| RST after the peer's FIN | "Reset a stream immediately"; no rule for the reads | the reads drain, then EOF: the RST moves only a read state that is still open (`stream.go`, lines 439 to 442) | the reads drain, then EOF (`yamux/src/connection.rs`, line 604; `yamux/src/connection/stream.rs`, lines 353 to 356) | the reads drain, then EOF, also behind bytes the core holds; the RST ends the write direction (`Entry.onFrame`) ("an RST after the peer's FIN leaves the reads to drain to EOF") |
| RST on a window update | no length meaning | the length is an error code (`stream.go`, lines 436 and 437) | not checked | read as a reset; we send 0 ("the peer's RST ends the stream with a reset") |
| session close | go-away "should be sent" | `Close` sends none; `CloseWithError` sends one with its code (`session.go`, lines 283 to 295) | not checked | go-away, normal code ("after our go-away, opens are refused and SYNs reset") |
| ping echo under load | silent | dropped past `PingBacklog`, 32 (`mux.go`, line 72; `session.go`, lines 803 to 806) | one pending control frame; the reader stops until it is sent (`yamux/src/connection.rs`, lines 412 to 421 and 461 to 477) | dropped beyond `controlQueueCap` ("a ping flood leaves the control queue at its cap") |
| our ping with no pong | silent | `ErrTimeout` after `ConnectionWriteTimeout`, 10 s (`session.go`, lines 428 to 436) | not checked | `.error .timeout` after `pingDeadlineMs`, 10 s ("a ping that no pong answers fails with timeout at its deadline") |
| keepalive | silent | after 30 s with no bytes, a ping; a failed ping closes the session, with no go-away (`mux.go`, lines 73 and 74; `session.go`, lines 459 to 471; go-libp2p v0.50.0 keeps the default, `vendor/go-libp2p`, `p2p/muxer/yamux/transport.go`, lines 17 to 34) | not checked | the same, on the ticks; the session ends with `timeExpired` and no go-away ("a keepalive with no pong ends the session with a fault") |
| reads ahead of the frame in hand | silent | under go-libp2p, no buffer of its own; the Noise session holds one decrypted message (`vendor/go-libp2p`, `p2p/muxer/yamux/transport.go`, line 29; `p2p/security/noise/rw.go`, lines 39 to 86) | not checked | one connection read: over Noise, one decrypted message (the reader's credit) ("the reader reads no further ahead than the read the loop takes") |

Two rows were also checked against js-libp2p and nim-libp2p. Data
after the peer's FIN: js takes it with no error, charges it, and hands
it on (`vendor/js-libp2p/packages/stream-multiplexer-yamux/src/stream.ts`,
lines 213 to 222). RST with bytes the reader has not taken: nim clears
its queues (`reset`, `vendor/nim-libp2p/libp2p/muxers/yamux/yamux.nim`,
line 246).

### Where this package differs from go-yamux and rust-yamux

No answer differs from both. Where the two disagree, the table above
names the side this package takes.

## How this package reads a root rule

**"A retired id is never reused"** (root §3.3, the invariants that
become theorems; root §6, layer 1). To reuse an id is to assign it
again, and a session assigns only its own ids: each side numbers its
own streams, by parity. So the rule is about our ids, and `stepRetired`
proves it as written. The rule does not ask the session to refuse a
peer that opens one of its own ids again, and the session must not
refuse it (the evidence is below). A reopened peer id gets a new
`StreamKey`, and `stepRetiredKey` and `stepStale` show that no handle
of the old stream reaches the new one. Why the peer's ids stay open:

- The spec asks no order of the peer's ids and forbids no reuse. It
  says "an initial data or window update frame is sent with a new
  StreamID", and of parity, "This prevents any collisions"
  (`vendor/specs/yamux/README.md`, "Opening a stream" and "StreamID
  Field").
- go-yamux sends the SYNs of concurrent opens out of id order.
  `OpenStream` takes its id with a compare-and-swap and sends the SYN
  later, outside the lock (`vendor/go-yamux/session.go`, lines 222 to
  241). Its `incomingStream` refuses an id only while it is live (lines
  869 to 877).
- rust-yamux checks the parity of a remote id alone
  (`is_valid_remote_id`, `vendor/rust-yamux/yamux/src/connection.rs`,
  lines 887 to 895), and opens any id that is not in its table (lines
  617 to 639).
- The go interop check opens four streams from four goroutines
  (`scripts/yamux-interop/main.go`, lines 120 to 124), and the core
  takes SYNs in any order (`Tests/Yamux.lean`, "the peer's SYNs out of
  id order both open").
- Accepting SYNs in any order and refusing every retired peer id would
  need a record of every id below the highest one seen that has not
  opened yet. A peer that opens id `n` first leaves `n / 2` such ids,
  so no bounded table holds the record (§5.1).

## What the package must not depend on

- `net/streams` is the only import from its own group (§2, §7 row 9):
  the package reads and writes through `Connection` and serves the
  `Stream` seam.
- From `base`, what the loop needs: `Async`, `Chan`, `TaskSet`,
  `OnceRef`, `Clock`, `select`, and `withinDeadline` from `base/conc`. The `Clock`
  serves the writer's deadline and the ticker; the core sees time only
  as `Event.tick`. From
  `base/bytes`: the byte model, the shared `DecodeError`, and the
  `Codec` and `LawfulCodec` classes.
- Nothing from the `codec` group, and nothing from `crypto`. Every
  header field is fixed width, so the package needs no varint.
- No libp2p knowledge: no `ProtocolId`, no `Muxer` type, no
  multistream message. The `/yamux/1.0.0` id is named in `libp2p/mux`
  (W5.4), above the seam this package serves.
