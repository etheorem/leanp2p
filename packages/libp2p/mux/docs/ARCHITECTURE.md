# leanp2p libp2p mux: architecture

`libp2p/mux` holds the `Muxer` values that the ordered configuration
lists of §3.1 carry. The seam types live in `libp2p/core`, and this
package fills them (§3.1, §9, delta 10). yamux is the P0 value:
`Mux.yamux` assigns the `/yamux/1.0.0` id to the session of
`net/yamux`, a session that knows no libp2p (§4.9). mplex is the P2
value, later in the same package, kept for go interop. The eth2
networking spec removed mplex, so no consensus unit waits on it (§8).
The spike validated the yamux parity rule live against go-libp2p, and
the mplex identity rule against the go-mplex spec and in-process (go
v0.50 removed mplex, so the matrix's mplex cells were skipped). The
same node code ran under both muxers in-process and over loopback TCP
(PRINCIPLES 1.3).

## Modules

| Module | Holds, and why |
|---|---|
| `Libp2p/Mux.lean` | the root module; one import line per public submodule. It does not re-export the mock or the private test wire |
| `Libp2p/Mux/Constants.lean` | `Mux.yamuxId` (`/yamux/1.0.0`), `Mux.mplexId` (`/mplex/6.7.0`), `Mux.testId` (`/leanp2p/test-mux/1.0.0`), and `Mux.mplexMessageCap` (1 MiB); the named ids of §3.4 and the cap of §5.1, one home per fact (§3.8) |
| `Libp2p/Mux/Yamux.lean` | `Mux.yamux`, the yamux value over the session of `net/yamux`; the `Role` conversion below. Planned |
| `Libp2p/Mux/Mplex.lean` | the mplex message codec and `Mux.mplex` (P2, §8); the spike reference is `Conn/Mplex.lean` (§10 row 15, §7 row 10). Planned |
| `Libp2p/Mux/Test.lean` | `Mux.test : Muxer`, the independent test session under `Mux.testId`. Planned |
| `Libp2p/Mux/Test/Wire.lean` | the private header, frame, and incremental parser. Present. Internal, and tests import it directly |
| `Libp2p/Mux/Test/State.lean` | the pure owner-loop state and its transitions. Present. Internal, and tests import it directly. A transition returns actions for the runtime shell |
| `Libp2p/Mux/Mock/Core/ProtocolId.lean` | the temporary `ProtocolId`. Present. `Constants.lean` imports only this module, so the constants stay free of `Conc` and `Streams` |
| `Libp2p/Mux/Mock/Core.lean` | the temporary `Role`, `Error`, `Muxer`, and `MuxSession` that let W5.4 compile before W5.2. Present. The public root does not import it |

Public declarations live in the `Libp2p.Mux` namespace, and the root
module re-exports the public submodules. The private wire declarations
live in `Libp2p.Mux.Test.Wire`.

`Libp2p/Mux.lean`, `Libp2p/Mux/Constants.lean`,
`Libp2p/Mux/Mock/Core/ProtocolId.lean`, `Libp2p/Mux/Mock/Core.lean`,
`Libp2p/Mux/Test/Wire.lean`, and `Libp2p/Mux/Test/State.lean` are in
the tree. `Yamux.lean`, `Mplex.lean`, and `Test.lean` are the
remaining modules of this package.

## Public surface

- `Mux.yamux : Muxer` carries `id := Mux.yamuxId` and the core seam's
  `open : Role → Connection → ByteArray → ExceptT Core.Error Async
  MuxSession` (§4.9; the core pair, public surface). `Yamux.lean`
  converts `Role` as the decision below records, and the session entry
  of `net/yamux` then applies that package's parity. The `ByteArray`
  argument is the negotiation leftover. `open` hands it to the session
  entry as data, and the session loop turns it into the first `Event`
  (§4.7).
- The error mapping happens once, in `Yamux.lean`: the value lifts the
  session failure into `Core.Error` with one `Except.mapError` (§3.5).
  The upgrader and the host match on `Core.Error` alone.
- `Mux.test : Muxer` is the test session below. Callers use the
  `Muxer` and `MuxSession` seams. Its id is `Mux.testId`.
- `Mux.mplex : Muxer` is the P2 surface: `id := Mux.mplexId`, the pure
  message codec, and a session that keys streams by
  `(id, initiator)`. The declared message length is capped at
  `Mux.mplexMessageCap` (§5.1).
- `MuxSession.openStream` carries a `ProtocolId`; the decisions below
  record it (the core pair, public surface).

## Test session

### An independent test muxer

`Mux.test` is an independent deterministic test muxer. It sends a
private repository-only frame over `Connection`. The frame exists so
repository tests can predict every byte. It is not a standardized or
interoperable libp2p protocol. `Mux.test` is not an alias over Yamux.
Its id is `Mux.testId`, and
`Mux.testId.toString = "/leanp2p/test-mux/1.0.0"`.

### Boundary

The public value is `Mux.test : Muxer`. A caller sees the W5.2
`Muxer` and `MuxSession` seams. Frame types, parser state, stream ids,
terminal state, admission gates, and scheduling state are private.
They do not appear in public Lean declarations.

Temporary W5.2 types live only under `Libp2p/Mux/Mock/`.
`Mock/Core/ProtocolId.lean` holds `ProtocolId`, and `Constants.lean`
imports that module alone. `Mock/Core.lean` holds `Role`, `Error`,
`Muxer`, and `MuxSession`, so this package can compile before W5.2.
The four error arms are the categories in the core architecture.
Each arm carries a `String` as a provisional rendered payload.
`MuxSession.join` is the provisional name of the completion the owner
joins. W5.2 has not landed these declarations. When it lands, delete
both mock modules. The imports then move to the `Libp2p.Core` modules
that own the same names. The private test protocol is not part of
the mock.

### Owner-loop state

`Test/State.lean` is the pure state the owner loop steps. It holds
the parser, `nextLocal`, `nextRemote`, the live table, one
unacknowledged send, the admitted write queues, and the terminal
cause. A transition returns that state and an ordered list of
actions. The runtime shell performs the list in order.

`sendFrame` and `sendChunk` are intents. The pre-send state stays in
place until `ackSend` or `failSend`. `ackSend` commits the successful
write and emits its resolutions and permit returns. `failSend` claims
the writer fault with the caught `IO.Error`. It releases that send's
resources once. A later claim does not release them again. An
impossible acknowledgement or scheduler step returns `InvariantError`
and leaves the caller's state in place. The shell throws
`InvariantError.toIOError`. A peer error is `Core.Error`. A
connection fault is the `IO.Error` stored on the terminal cause.
Scheduling and writes states the one-send rule.

Each admitted write stores the `Nat` tag from `Streams.Completions`.
A chunk intent and a write resolution both carry that tag. The answer
is `Except Streams.Error Unit`, the completion-table value. A
write-permit action names the stream. An empty write registers a tag,
takes no write permit, enters no queue, and resolves from the port
mode the shell just read.

The shell calls `classifyRemote` before it reserves a live permit or
an accept permit. It reserves both only for an open that classifies
as the next remote id. It passes `gotAccept` only when the accept
channel has a free slot. Both reservations install the stream.
`enqueueAccept` transfers the accept reservation into the runtime
accept envelope. The consumer of that envelope returns the permit,
including after `closeAccept` and after the owner has returned.
Reset, fin, and removal from the live table do not return it. A
refusal is a reset intent. `ackSend` retires that id and returns each
permit the refusal still holds. A zero, wrong-parity, duplicate, or
future open is classified first, so that open acquires no permit.
`pull` returns at most one parser budget of frames and does not admit
them. `inboundEnd` does not run while the parser still holds a
complete frame.

A reader or writer fault stores its `IO.Error`. The terminal action
carries that cause. `Cause.fault?` is the value passed to
`Outcome.recordFault`. A later fault does not replace it.

`setPort` publishes `halfClosed`, `reset`, or `sessionClosed` before
`closeWritePermits` for the same id. `closeInbox` is the read side
and stays a separate action. A clean close and a capacity refusal
emit no `setPort`. A port that is already `reset` stays `reset` when
the session closes, and that close does not close the write-permit
channel again. Absence from the live table is retirement.

The state does not store a waiting caller, a channel, a task, or an
atomic cell. A local open in a transition already holds a live permit.
A write already holds a write permit. `reset` replaces an open or
half-closed write mode, and a repeated reset stays reset.
`sessionClosed` does not become `reset`. A reset mode stays reset
when the session closes.

### Private frame

The header is nine bytes. The payload follows it.

| Field | Width | Encoding | Meaning |
|---|---:|---|---|
| kind | 1 byte | `1=open`, `2=data`, `3=fin`, `4=reset` | whole discriminator |
| stream id | 4 bytes | unsigned big-endian | nonzero stream id |
| length | 4 bytes | unsigned big-endian | payload byte count |
| payload | `length` bytes | raw bytes | data frames only |

An open, a fin, and a reset require length zero. A data frame requires
a length in `1 … testPayloadCap`. The frame has no version, flags,
acknowledgement, session-close, or protocol-id field. Closing the
session closes the underlying `Connection`. `openStream` accepts a
`ProtocolId`, and this muxer does not encode it.

### Policy constants

These values are repository-test policy. They are not standardized
protocol values. `testPayloadCap` is not `Mux.mplexMessageCap`.

| Constant | Value | Reason |
|---|---|---|
| `testPayloadCap` | `16 * 1024` | Caps one data payload of this test session |
| Live streams | 32 | Caps the streams the session holds at once |
| Accept backlog | 16 | Caps inbound streams waiting for `accept` |
| Inbound frame credit | 4 | Caps unread frames queued on one live stream |
| Event channel | 32 | Caps events waiting for the one owner loop |
| Admitted writes | 4 | Caps writes the session has admitted on one stream |
| Parser frame budget | 8 | Caps the complete frames one turn takes from the parser |

### Stream ids

An initiator session issues odd ids, starting at `1` and advancing by
two. A responder session issues even ids, starting at `2` and advancing
by two. The first three initiator ids are `1`, `3`, and `5`. The first
three responder ids are `2`, `4`, and `6`. A new session starts again
at the first id of its role. Zero stays unused.

`nextLocal` and `nextRemote` are non-wrapping `Nat` high-water values.
A remote open matches the sequence only when its id equals
`nextRemote` and its parity is the remote parity. A skipped, future,
wrong-parity, zero, or duplicate open is a protocol error. The last
odd id `2^32 - 1` and the last even id `2^32 - 2` may each be issued
once. After `nextLocal` or `nextRemote` exceeds `UInt32.max`, the
session issues no new id and accepts no new id.

When a remote open matches that next id, the owner loop reserves one
live permit and one accept permit. The accept permit comes from a
channel of `acceptBacklogCap` tokens, so a full backlog never reserves
it. If both succeed, the stream enters the live table, `nextRemote`
advances by two, and `enqueueAccept` transfers the accept reservation
into the runtime accept envelope. If either reservation fails, the
session sends reset. After that send returns, `nextRemote` advances
by two and each acquired permit is returned. The refused id stays out
of the live table. The live cap and the accept cap are consulted only
for a valid remote open.

A local open that is waiting for admission does not read or advance
`nextLocal`. It exposes no id. The session takes the id only when
admission succeeds. If the session shuts down while the open waits,
the open fails and still takes no id.

The Yamux adapter decision below records the same odd and even
partition for Yamux. The test session uses the partition so the two
ends of one pair can open at the same time and still receive different
ids. The test session does not implement Yamux.

### Stream lifetime

The live table holds streams that are open now. It holds no tombstone
for an id that has gone.

A local reset or a received reset aborts both directions for new
operations. The id retires at once. No new inbound data is admitted.
No new write succeeds. The session does not echo a received reset.
Admitted writes complete with `Streams.Error.reset`. Bytes already
accepted into the inbox stay readable. After those bytes drain, one
read returns `Streams.Error.reset`. The following read returns
`.ok none`. The session records reset on the stream port before it
closes the inbox. The stream handle may still drain that inbox after
the id has retired. Session close records session close on the port
before the inbox closes. A port that already records reset stays
reset. A clean close and a refused remote open leave the port unset.

A received fin closes the remote write direction. The inbox closes
at that fin. Bytes already queued stay readable. The application
reads them, and the next read answers `.ok none`. This holds whether
or not the local write direction is still open.

Local half-close closes the local write direction only after the
flush in Scheduling and writes. The id leaves the live table only
when both write directions are closed. The inbox outlives that
removal, so the drain and the EOF stay observable.

A second fin for a direction that is already closed is ignored. Data
that arrives after a received fin is ignored. The session stays up.
Data for a read direction that is still open is delivered.

An id with its opener's parity, below that opener's high-water value,
and absent from the live table, is retired. `nextLocal` is the local
high-water value. `nextRemote` is the remote high-water value. A
data, fin, or reset frame for a retired id is ignored. An open for a
retired id is a duplicate open and a protocol error. A data, fin, or
reset frame for an id that was never opened is a protocol error. An
id is never reused.

### Parser and codec

The header codec and the frame codec cover values their types can
construct. The parser performs the semantic checks. It checks a
declared payload length against `testPayloadCap` before it retains
the body. An unknown kind, an id of zero, a control length other than
zero, a data length of zero, or a data length above the cap fails at
that check.

One pull emits at most `parserFrameBudget` complete frames. The
private wire module is the home of that constant. A later pull emits
a complete frame the first pull kept. It needs no new connection
bytes. A partial body stores the bytes already received and the
length still required. The next chunk does not encode that header
again.

A partial header or a partial body waits while the connection stays
open. A connection end during a partial header or body is a protocol
error. A connection end with an empty parser is the connection-end
cause. `Connection.read = none` is a connection end. The seam does not
distinguish a peer FIN, a peer RST, and a local close.

### Ownership

One reader task and one owner loop serve the session. The loop is the
only task that steps the pure session state, and it is the only task
that writes a frame. Callers post events on the bounded event channel.
The loop is the only caller of `Outcome.finish`. `TaskSet.joinAll`
returns before `Outcome.answer`. The reader and the loop catch an
`IO.Error` from the connection and return. `joinAll` therefore does
not throw that error a second time.

The owner does not cancel either task. Shutdown closes the connection
and the event channel, and that close wakes a parked task. Stream
inboxes and completion tags wake parked callers on reset and during
teardown. The session retains a caller's write array only while that
admitted write is still pending.

### Terminal causes

The private terminal causes are running, owner close, connection end,
an IO fault that carries its `IO.Error`, and a protocol failure that
carries its `Core.Error`.

The first atomic claim out of running wins. A later cause leaves the
winner in place. Only a winning owner close calls
`Outcome.markClosing`. No claimant writes fault state into `Outcome`.
Teardown records a winning IO fault once, through `Outcome.recordFault`,
before `Outcome.finish`.

`Core.Error` is the seam error named in the root architecture (§4.9).
This package does not declare it.

Owner close and connection end call `Outcome.finish (.ok ())`.
No fault is recorded. `Outcome.answer` returns that success.

An IO fault calls `Outcome.finish (.ok ())` after the one
`recordFault`. `finish (.ok ())` stores a successful protocol result.
That result carries no protocol error. `Outcome.answer` throws the
previously recorded `IO.Error`.

When a protocol failure wins, teardown calls
`Outcome.finish (.error protocolError)`. `Outcome.answer` returns
that protocol error. A later cause does not alter the winner, and
teardown does not record an IO fault for it.

Teardown that still sees running is an internal invariant failure.
It throws. It does not call `Outcome.finish`.

An empty parser selects connection end. A partial frame selects a
protocol failure. That split is fixed under Parser and codec.

Teardown releases the waiters. A pending open completes with the
closed arm of `Core.Error` on owner close, connection end, and an IO
fault. It completes with the stored `Core.Error` on a protocol
failure. A stream write completes with `Streams.Error.reset` when
that stream is reset, and with `Streams.Error.closed` when the session
ends the write for any other cause. Scheduling and writes records the
same closed result for a write that `Connection.write` itself fails.
Teardown closes every live inbox and every inbox still queued for
`accept`, so a parked read wakes.

### Scheduling and writes

A turn processes at most one available event. It then takes at most
the parser frame budget of complete frames, then one outbound chunk.
One chunk is at most `testPayloadCap` bytes. A large write cannot
hold the connection for the rest of its bytes.

A complete frame already in the parser, or an outbound chunk that is
ready, keeps the loop runnable when no new event is queued. The loop
parks only when a queued event, a complete buffered frame, and a
ready outbound chunk are all absent.

The owner performs one `sendFrame` or `sendChunk`. It then calls
`ackSend` or `failSend`. Only then does it dequeue and apply another
event. The event stays queued while the send is open. `pump` emits
nothing during that send. `resetLocal`, `resetRemote`, `openRemote`,
`dataRemote`, `finRemote`, and `apply` return
`InvariantError.sendInFlight` if they are called in that window. A
correct shell never observes that error. If it does, the shell
throws `InvariantError.toIOError`.

`openLocal` is the caller-owned exception. The call already holds a
live permit, so it completes that opener with `closed` and returns
the permit. The in-flight send stays. `openRemote` is reserved before
the call. `sendInFlight` from `openRemote` is unreachable when the
shell follows this order. When that error is returned, the caller
still owns those permits and releases them while the invariant is
thrown.

Streams that have admitted bytes take turns. Writes on one stream
keep their admission order. One logical write is split into private
chunks. The state records each chunk only after `ackSend`. The write
resolves when its last chunk is acknowledged. An empty write registers
a completion tag, takes no write permit, and resolves at once from the
port mode.

A stream admits at most the admitted-write cap of writes. A further
writer waits outside the admitted queue, on the write-permit channel.
Half-close, reset, and session shutdown publish the port mode and
then close that channel. The actions are `setPort` and then
`closeWritePermits`. A later close of the same stream emits neither
again. The waiting writer wakes and completes from the port cell:
`closed` after half-close or session shutdown, and `reset` after
reset. A local half-close stops admission. Writes already admitted
flush. The session sends fin after that flush is acknowledged. A
flush that throws follows the `Connection.write` rule below, and no
fin is sent. A write that arrives after the half-close, including an
empty write, completes with `Streams.Error.closed`.

`Connection.write` throws `IO.Error` and tears the connection down.
The logical `Stream.write` has no arm for that error. The loop
resolves that write, and every write still waiting, with
`Streams.Error.closed`. `Connection.write` does not say whether the
peer received the bytes. When the IO fault won the terminal claim,
`Outcome.answer` throws the stored `IO.Error`. When owner close
already won, `markClosing` has ended the outcome, the fault is not
recorded, and `answer` returns success. The stream write is
`Streams.Error.closed` in both cases.

A local reset sends one reset frame. Admitted writes, and writes
still waiting for admission, complete with `Streams.Error.reset`.
Stream lifetime records a received reset and the moment the id
leaves the live table.

### Accept and backpressure

The accept backlog holds at most its cap of inbound streams. The
runtime accept channel is that backlog. `enqueueAccept` puts one
envelope on it, and the envelope owns the accept reservation.
`accept` receives the envelope and returns the reservation.
`Chan.close` leaves queued envelopes readable, so `accept` can still
receive them after `closeAccept` and after the owner has returned. A
drain of that channel returns each envelope's reservation once.
Reset, fin, and ordinary stream teardown do not return it and do not
remove the envelope. Each live stream queues at most the inbound
frame credit of unread frames. The owner loop does not park on a
stream inbox.

A full inbox resets that live stream only. A remote open that finds
the accept backlog or the live-stream cap full follows the refusal
rule in Stream ids. The session stays up. A local open past the
live-stream cap waits. Stream ids records that this wait takes no id.

After terminal shutdown has linearized, `accept` returns no newly
accepted stream. Entries already buffered stay readable. The caller
that receives one, or that drains the channel, returns its
reservation. A stream accepted immediately before that point may
still be returned. The caller then sees its inbox close.

### Resources

One byte subtotal is calculable. It counts these copies. Each copy
is counted where it currently sits:

- copied inbound slices in the event channel, each at most
  `testPayloadCap` bytes;
- parser-owned bytes: one incomplete frame, the slice being appended,
  and one extra slice;
- one outbound frame: its header and at most `testPayloadCap` payload
  bytes;
- inbox payloads: at most the live-stream cap times the inbound frame
  credit, each at most `testPayloadCap` bytes.

The session states no bound on process memory. The subtotal above is
the only byte total the session accounts.

The event channel bounds how many events wait. It does not bound the
bytes of every event. A copied inbound slice in the channel is inside
the subtotal. A write event retains the caller's array. The count of
admitted writes is at most the live-stream cap times the
admitted-write cap. The length of each retained array is the
caller's, and it has no session cap.

`Connection.read` may return an array of any positive length. `feedB`
does not reject a chunk because of its size. The session preserves the
copied-byte subtotal by feeding slices no larger than `testPayloadCap`.
The original array stays outside that subtotal while the reader owns it.

A caller parked outside admission holds its own array until the call
returns. The count of those callers has no session cap. Maps,
channels, tasks, objects, and allocator overhead sit outside the
subtotal.

### Errors

A malformed private frame and an invalid stream sequence are protocol
errors of this package. The session maps them to the protocol arm of
`Core.Error` (§3.5, §4.9). An open that cannot take an id receives
that same error, and the session stays up.

A stream reset completes with `Streams.Error.reset`. A stream
operation after the stream or the session has closed completes with
`Streams.Error.closed`. Terminal causes records which of success, a
thrown `IO.Error`, or a returned `Core.Error` the session owner
observes, and how pending opens are released. A full admission cap
leaves the session open.

## Owned contracts and how the package keeps them

1. **The seam carries `id : ProtocolId`, and code compares ids
   only** (§3.1, §3.4). The string literals `/yamux/1.0.0`,
   `/mplex/6.7.0`, and `/leanp2p/test-mux/1.0.0` appear in
   `Constants.lean` and in no production code. The negotiator sees
   `ProtocolId` values.
2. **A seam value holds no protocol decisions** (§3.1). `Mux.yamux`
   moves the role, the connection, and the leftover into the session
   entry of `net/yamux`, and maps the error back. The frames are that
   package's business.
3. **Lifecycle is part of the seam** (§3.1, §4.1). The `MuxSession`
   each value returns exposes `close : IO Unit` and the session
   completion, and the owner closes and then joins.
4. **Half-close follows the spec exactly, in yamux and mplex** (§5.3,
   PRINCIPLES 2.2). Close ends the write direction of the closer, and
   the read direction keeps working, so the response after our FIN
   still arrives. Reset aborts both directions. The yamux session
   carries its own half-close suite in `net/yamux` (the yamux pair,
   plan); the mplex suite of the plan pins the same sentence, with the
   case the spike's old test missed. The test session's half-close is
   under scheduling and writes.
5. **The mplex identity rule is the go-compatibility contract**
   (§4.9). Both sides number their streams from zero, so an id alone
   names no stream, and the session keys every stream by
   `(id, initiator)`. The flag bit routes each inbound message to the
   key it names. The spike validated the rule against the go-mplex
   spec, in-process, and the suite keeps the validation.
6. **The 1 MiB cap is checked before allocation** (§5.1,
   PRINCIPLES 2.3). `Mux.mplexMessageCap` names that 1 MiB limit.
   `Constants.lean` owns it, beside the ids. A declared length over
   the cap is a protocol error, and it tears the session down.
   `Mux.mplex` rejects that length before allocation.

## Decisions

- **The yamux session lives in `net/yamux`, and the value lives
  here** (§4.9). The session knows no libp2p, so a libp2p-free
  consumer can use it, and the id assignment stays a one-line decision
  at the seam (§9, delta 10). A new muxer lands as a new value, with
  no edit to the upgrader (PRINCIPLES 1.3).
- **`Libp2p/Mux/Yamux.lean` converts `Role`, and the Yamux session
  applies parity.** The core pair folded the spike's client and server
  entries into one `open` field (the core pair, decisions). The
  adapter then maps the role. `Core.Role.initiator` selects the Yamux
  client side, which opens odd ids, starting at `1` and advancing by
  two. `Core.Role.responder` selects the Yamux server side, which
  opens even ids, starting at `2` and advancing by two. Yamux reserves
  stream id `0` for session messages. An inbound SYN creates a stream
  when its id has the remote parity. A SYN whose id has the local
  parity creates no stream state. `Libp2p/Mux/Yamux.lean` translates
  `Core.Role` to the side selector that the final W4.3 public API
  exports. `net/yamux` keeps its own client and server sides and
  imports no libp2p module.
- **`MuxSession.openStream` takes a `ProtocolId`.** The spike's
  `MuxHandle.openStream` took the name, mplex put it in its NewStream
  frame, and the other muxers ignored it (§10 row 12; the core pair,
  plan). §3.4 calls a bare `String` a smell, and every real caller
  passes a protocol id, so the seam carries the id. The seam keeps one
  signature, so `Mux.yamux`, `Mux.mplex`, and `Mux.test` stay
  interchangeable at every call site. The yamux value drops the id
  before it calls the session of `net/yamux`, whose SYN frame has no
  field for it. The test session drops the id. The mplex wire
  label is the id's string form: the frame carries the name as its
  data, a label the spec gives no semantic value.
- **mplex is P2 and stays in this package's plan** (§8). The eth2 spec
  removed it, so consensus never waits, and older go-libp2p peers and
  other stacks still speak it, so the interop surface of §4.9 stays
  real. Root PLAN W5.4 carries the unit, and §7 row 10 puts mplex last
  inside the libp2p row.

## What the package must not depend on

- Inside libp2p, `core` only (§2: core → {security, mux}). No import
  of `libp2p/security`, `libp2p/negotiate`, `libp2p/host`,
  `libp2p/protocols`, or `libp2p/identity`. A muxer knows no
  `PeerId`, and the `MuxSession` surface names only streams.
- From the net group, `net/yamux` and `net/streams` (§2). The yamux
  value imports the session entry of `net/yamux`. The mplex session
  and the test session import `Connection` and the `Stream` seam, and
  the test session does not import `net/yamux`. `core` defines no
  re-export for `Connection`, so these modules import `net/streams`
  directly and record the import here, per the core pair's rule (the
  security pair records the same import).
- From the codec group, `codec/varint` only: the mplex header and
  length are uvarints, and §2's group chain puts `codec` to the right
  of `libp2p`.
- From `base`, what the mplex and test loops need: `Async`, `Chan`,
  `TaskSet`, and `OnceRef` from `base/conc`, and the byte model,
  `DecodeError`, and the `Codec`/`LawfulCodec` classes from
  `base/bytes`, the sets the yamux pair lists for the same job.
- No crypto. The muxer runs after security and moves plaintext, and no
  field names a key, a hash, or a cipher.
