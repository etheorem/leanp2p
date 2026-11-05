import Bytes.Blob
import Streams.Error
import Yamux.Constants
import Yamux.Sets
import Yamux.Header

/-!
# The yamux core

A yamux session is a pure state machine (ARCHITECTURE §3.3):

```
step : State → Event → Except ProtocolError (State × List Action)
```

`State`, `Event`, and `Action` are plain data. They hold no `IO.Ref`,
no `Task`, no promise, and no function, so a test compares them by
value. The loop task of `Yamux.Loop` owns one `State`, turns every input
into an `Event`, and performs the `Action`s. The core never calls `IO`
and never reads a clock: time arrives as `Event.tick` (ARCHITECTURE,
"Decisions"; root §3.3).

## Inputs and outputs

The `Event`s: bytes off the connection (the plaintext that the muxer
negotiation over-read arrives the same way, as the first event); the
end of the connection; a tick of the clock; and the operations of the
application: open, write, consume, close, reset, ping, go away.

The `Action`s: send a frame; send a ping echo that the shell may drop;
send the answer to a SYN, under back-pressure; deliver bytes to a
stream; end a stream's reads by EOF or by a
reset; offer a new inbound stream; answer an open, a write, or a ping by
its tag; park and wake writers; ask for a tick; end the session for a
keepalive that the peer did not answer; shut the session down.

## Time

The spec fixes no timer. go-yamux runs two on the session, and the core
runs them on the ticks: a ping that no pong answers within
`pingDeadlineMs` fails (`Ping`, `vendor/go-yamux/session.go`, lines 412
to 436), and
after a keepalive interval with no bytes from the peer the session
pings, and ends when that ping fails (`startKeepalive`, lines 446 to
471; bytes from the peer restart the interval, line 734). The host owns
the keepalive policy, so the interval is a parameter of the session.

The core knows the time from the latest `Event.tick` alone. The shell
posts a fresh tick right before the events that start a timer, our ping
and the bytes of a read, so each timer counts from the right moment.
Nothing in the session polls (root §3.3): after each step the core asks
for a tick at its next deadline (`Action.wakeAt`), and the shell sleeps
until then.

## The receive path

Bytes arrive in chunks of any size, so the core keeps a receive cursor,
`Rx`: the header bytes seen so far, or the rest of a data payload. The
core reads a header as soon as its 12 bytes are present, and decides
the frame then. A data frame is checked against the receive window of
its stream at the header, before the shell buffers one payload byte
(owned contract 1). The payload then streams through as `deliver`
actions, with no copy held in the state.

## The window fact

An entry carries `windowOk : recvWindow + unread ≤ initialWindow`, the
proof-carrying form of §3.7. `recvWindow` is the credit the peer still
holds, and `unread` counts the bytes delivered that the application has
not consumed. Every update of the two fields must prove the fact again,
so the core cannot accept a byte beyond the window: the proof needs the
check `length ≤ recvWindow`. The fact also bounds the bytes that one
stream buffers by the window.

## The send path

The core holds no parked write; the shell parks the writers (owned
contract 4). A write sends what the credit covers, in frames of at most
`maxDataFrame`. When all of it went, the core answers `done` after the
last frame, and the shell answers the writer once that frame has gone
to the connection. When the credit ran out first, the core answers
`blocked` with the count it sent, and the writer parks with the rest.
The core signals `credit` when a window update grants credit, and when
a write completes with credit left. The shell then wakes one parked
writer, if one waits, so the rest of a grant reaches the next writer.
-/

set_option autoImplicit false

namespace Yamux

open Bytes

/-! ## Data types

The core's bytes sit in `Bytes.Blob`, the shared wrapper with a
`Repr` (§3.2). -/

/-- The side of the session. The client numbers its streams odd, the
server even (spec, "StreamID Field"). The muxer value of the layer above
maps its own role onto this one. -/
inductive Role where
  /-- The dialer: odd stream ids. -/
  | client
  /-- The listener: even stream ids. -/
  | server
  deriving DecidableEq, Repr, Hashable

namespace Role

/-- The parity of the ids this side opens: 1 for odd, 0 for even. -/
def parity : Role → Nat
  | .client => 1
  | .server => 0

/-- The first id this side opens. 0 is the session's id, so the server
starts at 2. -/
def firstId : Role → Nat
  | .client => 1
  | .server => 2

/-- The first id of a role has the role's parity: the client starts odd
and the server even ("StreamID Field"). -/
theorem firstIdParity (r : Role) : r.firstId % 2 = r.parity := by
  cases r <;> rfl

/-- The other side. -/
def other : Role → Role
  | .client => .server
  | .server => .client

/-- Two sides with one parity are one side. -/
theorem eqOfParityEq {a b : Role} (h : a.parity = b.parity) : a = b := by
  cases a <;> cases b <;> simp_all [parity]

end Role

/-- A stream id, the proof-carrying form of §3.7: the id, the side that
opened the stream, and the facts the spec fixes. The id has the parity
of its opener ("The client side should use odd ID's, and the server
even"), it is not 0, which "is reserved to represent the session", and
it fits the 32-bit field. The core checks a peer's id once, where the
SYN enters (`StreamId.ofRemote?`); from there on the type carries the
facts. -/
structure StreamId where
  /-- The id on the wire. -/
  val : Nat
  /-- The side that opened the stream. -/
  opener : Role
  /-- The id has the opener's parity. -/
  parity : val % 2 = opener.parity
  /-- The id is not the session's. -/
  pos : 0 < val
  /-- The id fits its 32 bits. -/
  lt : val < streamIdLimit
  deriving DecidableEq, Repr

/-- The id `n` of a SYN the peer sent, when the peer may open it: the
peer's parity, and not 0. `none` for any other id. -/
def StreamId.ofRemote? (role : Role) (n : Nat) (hlt : n < streamIdLimit) : Option StreamId :=
  if h : n % 2 ≠ role.parity ∧ 0 < n then
    some ⟨n, role.other, by cases role <;> simp only [Role.other, Role.parity] at h ⊢ <;> omega,
      h.2, hlt⟩
  else none

/-- How the peer broke the protocol (§3.5). Each one ends the session. -/
inductive ProtocolError where
  /-- A header with a version other than 0, or an unknown type. -/
  | malformedHeader
  /-- A data frame longer than the receive window of its stream: the
  stream id, the declared length, and the window. -/
  | windowExceeded (streamId length window : Nat)
  /-- A SYN for a stream that is live. -/
  | duplicateStream (streamId : Nat)
  /-- A SYN on an id the peer may not open: an id of our parity, or 0,
  which the spec reserves for the session ("StreamID Field"). The
  session ends, as at go-yamux ("both yamux endpoints are clients",
  `incomingStream`, `vendor/go-yamux/session.go`, line 846) and
  rust-yamux (`vendor/rust-yamux/yamux/src/connection.rs`, lines 619 to
  621). go sends no go-away (`recv`,
  lines 691 to 694); rust and this core send the protocol-error code,
  since the spec says a go-away "should be sent" when a session ends
  ("Session termination"). Both check the parity alone, so on id 0 a
  client of theirs opens a stream and a server refuses; the spec's
  reservation decides that case here. -/
  | invalidStreamId (streamId : Nat)
  /-- The peer ended the session with an error code. -/
  | goAway (code : GoAwayCode)
  /-- A go-away with a code the spec does not define. -/
  | unknownGoAwayCode (code : Nat)
  deriving DecidableEq, Repr

/-- The go-away code that we send for an error we detected. `none` for
the peer's own go-away: the peer has ended the session already. -/
def ProtocolError.reply? : ProtocolError → Option GoAwayCode
  | .goAway _ => none
  | _ => some .protocolError

/-- What changes on one live stream. The id and the side of the stream
live in its `Entry`, outside this structure, so an operation that
returns a new `StreamState` cannot change them. -/
structure StreamState where
  /-- For a stream we opened: the peer's ACK arrived. For an inbound
  stream: we sent the ACK. -/
  acked : Bool
  /-- Our write direction is open: we sent no FIN and no RST. -/
  sendOpen : Bool
  /-- The peer's write direction is open: no FIN arrived. -/
  recvOpen : Bool
  /-- The bytes we may still send. -/
  sendCredit : Nat
  /-- The bytes the peer may still send. -/
  recvWindow : Nat
  /-- The bytes received that the application has not consumed: those in
  the inbox, and those `held` behind it. -/
  unread : Nat
  /-- The window fact (module doc). -/
  windowOk : recvWindow + unread ≤ initialWindow
  /-- The chunks in the stream's inbox that the application has not
  taken. -/
  slots : Nat
  /-- The inbox holds at most `inboxChunks` data chunks: it is the
  bounded `Chan` of ARCHITECTURE §3.3. -/
  slotsLe : slots ≤ inboxChunks
  /-- The bytes in the inbox that the application has not taken. -/
  inInbox : Nat
  /-- The bytes received while the inbox was full, joined into one
  chunk. -/
  held : Blob
  /-- The bytes the reader holds or waits for are bytes the window
  charged. With `windowOk`, a stream buffers at most the window. -/
  bufferedLe : inInbox + held.bytes.size ≤ unread
  /-- The peer's FIN arrived while bytes were held: the EOF goes to the
  reader after them. -/
  eofDue : Bool
  deriving DecidableEq, Repr

/-- The name of one stream for the application: its id and its epoch.
The peer may open an id again after it retired (the receive path), so
the id alone does not name a stream. The epoch counts the streams of the
session, and each stream gets the next one, so no two streams of a
session share a key. The `Stream` handle posts its events under its key,
and an event for a stream that has retired matches no entry. -/
structure StreamKey where
  /-- The stream id on the wire. -/
  id : Nat
  /-- The stream's place in the session's count of streams. -/
  epoch : Nat
  deriving DecidableEq, Repr, Hashable

/-- One live stream: its id, which names its opener, its epoch, and its
state. -/
structure Entry where
  /-- The stream id. -/
  id : StreamId
  /-- The epoch of the stream (`StreamKey`). -/
  epoch : Nat
  /-- The state that the operations change. -/
  state : StreamState
  deriving DecidableEq, Repr

/-- The key of the entry's stream. -/
def Entry.key (e : Entry) : StreamKey := ⟨e.id.val, e.epoch⟩

/-- The receive cursor. -/
inductive Rx where
  /-- Between frames: the header bytes seen so far, fewer than 12. -/
  | header (seen : Blob)
  /-- Inside a data payload: the stream, the bytes still to come,
  whether they go to the stream, and whether the frame carried FIN. -/
  | payload (streamId remaining : Nat) (deliver fin : Bool)
  deriving DecidableEq, Repr

/-- One of our pings in flight: its opaque value, the tag of the
application ping (`none` for a keepalive), and the time by which the
pong must arrive. -/
structure PingOut where
  /-- The opaque value of the ping frame. -/
  value : Nat
  /-- The tag of the application's ping; `none` for a keepalive. -/
  tag : Option Nat
  /-- The time by which the pong must arrive. -/
  due : Nat
  deriving DecidableEq, Repr

/-- The state of one session. -/
structure State where
  /-- Our side. -/
  role : Role
  /-- The live streams. -/
  streams : List Entry
  /-- The id of the next stream we open. It only grows. -/
  nextLocal : Nat
  /-- Our next id has our parity. -/
  nextLocalParity : nextLocal % 2 = role.parity
  /-- Our next id is not the session's. -/
  nextLocalPos : 0 < nextLocal
  /-- The epoch of the next stream, ours or the peer's. It only grows. -/
  nextEpoch : Nat
  /-- The receive cursor. -/
  rx : Rx
  /-- The open requests that wait for room in our ACK backlog. -/
  pendingOpens : List Nat
  /-- Our pings in flight. -/
  pings : List PingOut
  /-- The opaque value of the next ping. -/
  nextPing : Nat
  /-- We sent a go-away: no new stream, ours or the peer's. -/
  goneAway : Bool
  /-- The time of the latest tick (module doc, "Time"). -/
  now : Nat
  /-- The time of the latest bytes from the peer. -/
  lastRecv : Nat
  /-- The keepalive interval of the host's policy; `none` for no
  keepalive. -/
  keepalive : Option Nat
  /-- The tick the core asked for last. -/
  wake : Option Nat
  deriving DecidableEq, Repr

/-- An input of the core. -/
inductive Event where
  /-- Bytes off the connection, in arrival order. -/
  | bytes (b : Blob)
  /-- The connection ended. -/
  | eof
  /-- The clock reads `now`, in milliseconds. -/
  | tick (now : Nat)
  /-- The application opens a stream; the answer comes under `tag`. -/
  | openStream (tag : Nat)
  /-- The application writes to a stream; the answer comes under
  `tag`. -/
  | write (key : StreamKey) (tag : Nat) (b : Blob)
  /-- The application consumed `n` delivered bytes of a stream. -/
  | consumed (key : StreamKey) (n : Nat)
  /-- The application half-closes a stream. -/
  | close (key : StreamKey)
  /-- The application resets a stream. -/
  | reset (key : StreamKey)
  /-- The application pings the peer; the answer comes under `tag`. -/
  | ping (tag : Nat)
  /-- The application ends the session for new streams. -/
  | goAway
  deriving DecidableEq, Repr

/-- An output of the core. The shell performs the actions in order. -/
inductive Action where
  /-- Write the frame to the connection. -/
  | send (frame : Blob)
  /-- Write the echo of the peer's ping, or drop it when the control
  queue is full (owned contract 5): the peer can ping again. go-yamux
  drops a pong the same way (`vendor/go-yamux/session.go`, lines 803
  to 806). -/
  | control (frame : Blob)
  /-- Write the answer to the peer's SYN, the ACK or the RST that the
  spec demands. It is never dropped: when too many answers wait, the
  loop takes no more events until the writer has sent them, and TCP
  carries the back-pressure to the peer, as go-yamux blocks its receive
  loop on such a send (`vendor/go-yamux/session.go`, line 884). -/
  | reply (frame : Blob)
  /-- Hand the bytes to the reader of the stream. -/
  | deliver (streamId : Nat) (b : Blob)
  /-- The peer half-closed the stream: its reads end with EOF. -/
  | eof (streamId : Nat)
  /-- The stream was reset: its reads end with `.reset`. -/
  | reset (streamId : Nat)
  /-- Offer the new inbound stream to the application. -/
  | accept (key : StreamKey)
  /-- The open of `tag` gave the stream. -/
  | opened (tag : Nat) (key : StreamKey)
  /-- The open of `tag` failed. -/
  | openRefused (tag : Nat) (e : Streams.Error)
  /-- The write or the ping of `tag` completed. -/
  | done (tag : Nat)
  /-- The write of `tag` on stream `streamId` sent its first `n` bytes,
  all the credit there was. The shell parks the writer with the rest
  (owned contract 4). -/
  | blocked (streamId tag n : Nat)
  /-- Stream `streamId` has send credit. The shell wakes one parked
  writer, if one waits (owned contract 4). -/
  | credit (streamId : Nat)
  /-- The write direction of stream `streamId` ended with `e`. The shell
  closes the stream's credit channel, which wakes its parked writers
  (owned contract 7). -/
  | endWrites (streamId : Nat) (e : Streams.Error)
  /-- The write of `tag` failed. -/
  | refused (tag : Nat) (e : Streams.Error)
  /-- Post a tick at time `due`, or soon after: the next deadline of
  the core (module doc, "Time"). -/
  | wakeAt (due : Nat)
  /-- No pong answered the keepalive in time. The session ends with a
  fault and no go-away, as go-yamux closes it
  (`vendor/go-yamux/session.go`, line 470). -/
  | expired
  /-- The session ended without an error: the peer's normal go-away,
  or the end of the connection. -/
  | shutdown
  deriving DecidableEq, Repr

/-! ## Frames -/

/-- The SYN flag alone. -/
def synFlags : Flags := { Flags.none with syn := true }
/-- The ACK flag alone. -/
def ackFlags : Flags := { Flags.none with ack := true }
/-- The FIN flag alone. -/
def finFlags : Flags := { Flags.none with fin := true }
/-- The RST flag alone. -/
def rstFlags : Flags := { Flags.none with rst := true }

/-- A frame: the header, then the body. The stream id and the length
are below `2 ^ 32` at every call site (`Header.make`). -/
def frame (type : FrameType) (flags : Flags) (streamId length : Nat)
    (body : ByteArray := .empty) : Blob :=
  ⟨(Header.make type flags streamId length).encodeB ++ body⟩

/-- A window-update frame. The spec opens, closes, and resets a stream
with "a data or window update frame"; the core uses a window update with
a zero delta, which carries no payload. -/
def windowFrame (flags : Flags) (streamId : Nat) (delta : Nat := 0) : Blob :=
  frame .windowUpdate flags streamId delta

/-- The go-away frame with `code`, on the session id 0. -/
def goAwayFrame (code : GoAwayCode) : Blob :=
  frame .goAway Flags.none 0 code.toCode

/-! ## Stream operations

Each operation takes the entry and returns its new `StreamState` with
the actions. The id and the side stay in the entry, so no operation can
change them, and `State.put` stores the new state under the same id.
-/

namespace StreamState

/-- A new stream with the initial window both sides assume. An inbound
stream starts acknowledged: the core sends the ACK as it creates the
entry. -/
def fresh (outbound : Bool) : StreamState where
  acked := !outbound
  sendOpen := true
  recvOpen := true
  sendCredit := initialWindow
  recvWindow := initialWindow
  unread := 0
  windowOk := by simp
  slots := 0
  slotsLe := by simp
  inInbox := 0
  held := ⟨.empty⟩
  bufferedLe := by simp
  eofDue := false

/-- True while one direction is open, or while bytes and the EOF still
wait for the reader. A stream with both directions closed and nothing
left to hand over retires (owned contract 3). -/
def live (st : StreamState) : Bool :=
  st.sendOpen || st.recvOpen || st.eofDue

/-- Hand `chunk` to the reader of stream `id`: into a free inbox slot,
or behind the bytes already held. -/
def offer (st : StreamState) (id : Nat) (chunk : ByteArray) : StreamState × Array Action :=
  -- Only bytes the window charged reach the reader. `recvData` charges
  -- a frame before its payload streams through, so the check holds for
  -- every chunk, and it gives `bufferedLe` its proof. The `else` arm
  -- never runs: `Reachable.rxOk` and `offerKeeps` prove it.
  if hk : st.inInbox + st.held.bytes.size + chunk.size ≤ st.unread then
    if hfree : st.held.bytes.size = 0 ∧ st.slots < inboxChunks then
      ({ st with
          slots := st.slots + 1
          slotsLe := by omega
          inInbox := st.inInbox + chunk.size
          bufferedLe := by omega },
        #[.deliver id ⟨chunk⟩])
    else
      ({ st with
          held := ⟨st.held.bytes ++ chunk⟩
          bufferedLe := by simp only [ByteArray.size_append]; omega },
        #[])
  else (st, #[])

/-- Move the held bytes into a free slot, as one chunk, and the EOF
that waits behind them. -/
def flush (st : StreamState) (id : Nat) : StreamState × Array Action :=
  if hfree : st.held.bytes.size ≠ 0 ∧ st.slots < inboxChunks then
    ({ st with
        held := ⟨.empty⟩
        slots := st.slots + 1
        slotsLe := by omega
        inInbox := st.inInbox + st.held.bytes.size
        bufferedLe := by have := st.bufferedLe; simp only [ByteArray.size_empty]; omega
        eofDue := false },
      #[.deliver id st.held] ++ (if st.eofDue then #[.eof id] else #[]))
  else (st, #[])

/-- The application took one chunk of `n` bytes from the inbox: its slot
frees. A read takes bytes from the inbox, so it returns credit for those
alone: a count beyond them returns nothing more. -/
def take (st : StreamState) (n : Nat) : StreamState :=
  { st with
    slots := st.slots - 1
    slotsLe := by have := st.slotsLe; omega
    inInbox := st.inInbox - min n st.inInbox
    unread := st.unread - min n st.inInbox
    windowOk := by have := st.windowOk; omega
    bufferedLe := by have := st.bufferedLe; omega }

/-- Charge a data frame of `len` bytes, which the window admits, before
its payload streams through. The bytes that reach the reader count as
unread from here, so the window fact holds while they arrive. -/
def charge (st : StreamState) (len : Nat) (hw : len ≤ st.recvWindow) : StreamState :=
  { st with
    recvWindow := st.recvWindow - len
    unread := st.unread + (if st.recvOpen || st.eofDue then len else 0)
    windowOk := by have := st.windowOk; split <;> omega
    bufferedLe := by have := st.bufferedLe; split <;> omega }

end StreamState

namespace Entry

/-- The data frames of stream `id` that carry `b` from `pos` on, each of
at most `maxDataFrame` bytes, pushed onto `acts`. -/
def dataFrames (id : Nat) (b : ByteArray) (pos : Nat) (acts : Array Action) : Array Action :=
  if pos < b.size then
    let n := min maxDataFrame (b.size - pos)
    dataFrames id b (pos + n) (acts.push (.send (frame .data Flags.none id n (b.extract pos (pos + n)))))
  else acts
termination_by b.size - pos
decreasing_by
  -- `n` is above zero: the frame cap is, and so are the bytes left.
  have : 0 < maxDataFrame := by decide
  simp only [Nat.min_def]
  split <;> omega

/-- The application writes `p` under `tag`. The core sends what the
credit covers (module doc, "The send path"). -/
def write (e : Entry) (tag : Nat) (p : Blob) : StreamState × Array Action :=
  let st := e.state
  if !st.sendOpen then (st, #[.refused tag .closed])
  else
    let n := min st.sendCredit p.bytes.size
    let frames := dataFrames e.id.val (p.bytes.extract 0 n) 0 #[]
    let left := st.sendCredit - n
    let answer : Array Action :=
      if n = p.bytes.size then
        -- The write completes. Credit left over goes to the next parked
        -- writer, if one waits (owned contract 4).
        #[.done tag] ++ (if 0 < left then #[.credit e.id.val] else #[])
      else #[.blocked e.id.val tag n]
    ({ st with sendCredit := left }, frames ++ answer)

/-- The application took one chunk of `n` bytes from the inbox. Its slot
frees, and the held bytes move in. When the credit to return reaches
the threshold, a window update returns it, and the peer's credit grows
back to the full window less the bytes still unread. -/
def consume (e : Entry) (n : Nat) : StreamState × Array Action :=
  let (st, moved) := (e.state.take n).flush e.id.val
  if st.recvOpen && windowUpdateThreshold ≤ initialWindow - st.recvWindow - st.unread then
    ({ st with recvWindow := initialWindow - st.unread, windowOk := by have := st.windowOk; omega },
      moved.push (.send (windowFrame Flags.none e.id.val (initialWindow - st.recvWindow - st.unread))))
  else (st, moved)

/-- The application half-closes the stream: FIN goes out, and the
writers still parked wake with `closed`, since no data may follow the
FIN. -/
def closeLocal (e : Entry) : StreamState × Array Action :=
  let st := e.state
  if !st.sendOpen then (st, #[])
  else
    ({ st with sendOpen := false },
      #[.endWrites e.id.val .closed, .send (windowFrame finFlags e.id.val)])

/-- The application resets the stream: both directions end, the parked
writers wake with `reset` (owned contract 7), and RST goes out. -/
def resetLocal (e : Entry) : StreamState × Array Action :=
  let st := e.state
  ({ st with
      sendOpen := false
      recvOpen := false
      held := ⟨.empty⟩
      bufferedLe := by have := st.bufferedLe; simp only [ByteArray.size_empty]; omega
      eofDue := false },
    -- The local reset comes before the RST, so the peer never learns of
    -- a reset that our reader has not met yet.
    #[.endWrites e.id.val .reset, .reset e.id.val, .send (windowFrame rstFlags e.id.val)])

/-- The peer's FIN on stream `id`: its reads end with EOF, after the
bytes still held, if any. -/
def finRemote (id : Nat) (st : StreamState) : StreamState × Array Action :=
  if st.recvOpen then
    if st.held.bytes.isEmpty then ({ st with recvOpen := false }, #[.eof id])
    else ({ st with recvOpen := false, eofDue := true }, #[])
  else (st, #[])

/-- The body of a data frame for stream `id`: the window check, then the
receive cursor for the payload.

Data after the peer's own FIN breaks the spec's FIN ("the sender will
send no further data"), and the spec names no answer. go-yamux and
rust-yamux take it with no error, charge it to the window, and keep it
readable ahead of the EOF, and js does the same (the package
ARCHITECTURE, "Checked against the implementations"). The core does
the same while the EOF still waits behind held bytes; once
the reader has its EOF, the bytes pass by, since a `Stream` read ends
for good at its EOF. -/
def recvData (id : Nat) (st : StreamState) (h : Header) :
    Except ProtocolError (StreamState × Array Action × Rx) :=
  -- The window check, before any payload byte (owned contract 1).
  if hw : h.length ≤ st.recvWindow then
    let toReader := st.recvOpen || st.eofDue
    let st' := st.charge h.length hw
    if h.length > 0 then .ok (st', #[], .payload id h.length toReader h.flags.fin)
    else
      let (st', acts) := if h.flags.fin then finRemote id st' else (st', #[])
      .ok (st', acts, .header ⟨.empty⟩)
  else .error (.windowExceeded id h.length st.recvWindow)

/-- The body of a window update for stream `id`: the credit grows, and
while we still write, the shell may wake a parked writer. -/
def recvWindowUpdate (id : Nat) (st : StreamState) (h : Header) : StreamState × Array Action :=
  let acts : Array Action := if st.sendOpen && 0 < h.length then #[.credit id] else #[]
  let st := { st with sendCredit := st.sendCredit + h.length }
  let (st, fin) := if h.flags.fin then finRemote id st else (st, #[])
  (st, acts ++ fin)

/-- A data or window-update frame for this stream, after the SYN step:
the new state, the actions, and the receive cursor for the payload. The
flags apply in the order ACK, RST, the body, FIN. A FIN on a data frame
with a payload applies at the end of the payload. -/
def onFrame (role : Role) (e : Entry) (h : Header) :
    Except ProtocolError (StreamState × Array Action × Rx) :=
  -- The ACK answers a stream we opened.
  let st := if h.flags.ack && e.id.opener == role then { e.state with acked := true } else e.state
  if h.flags.rst then
    -- The payload of the frame, if any, passes by.
    let skip : Rx := if h.type == .data && h.length > 0 then .payload e.id.val h.length false false
      else .header ⟨.empty⟩
    let (st, acts) : StreamState × Array Action :=
      if st.recvOpen then
        ({ st with
            sendOpen := false
            recvOpen := false
            held := ⟨.empty⟩
            bufferedLe := by have := st.bufferedLe; simp only [ByteArray.size_empty]; omega
            eofDue := false },
          #[.endWrites e.id.val .reset, .reset e.id.val])
      else
        -- The peer's FIN came first, so its EOF stands: the reads end
        -- with EOF behind the bytes still held, as in go-yamux and
        -- rust-yamux (the package ARCHITECTURE, "Checked against the
        -- implementations"). The RST ends the write direction.
        ({ st with sendOpen := false }, #[.endWrites e.id.val .reset])
    .ok (st, acts, skip)
  else if h.type == .data then recvData e.id.val st h
  else
    let (st, acts) := recvWindowUpdate e.id.val st h
    .ok (st, acts, .header ⟨.empty⟩)

end Entry

/-! ## The stream table -/

namespace State

/-- A new session on our `role`, with the host's `keepalive` interval
(`none` for no keepalive), at time `now`. -/
def new (role : Role) (keepalive : Option Nat := none) (now : Nat := 0) : State where
  role
  streams := []
  nextLocal := role.firstId
  nextLocalParity := role.firstIdParity
  nextLocalPos := by cases role <;> decide
  nextEpoch := 0
  rx := .header ⟨.empty⟩
  pendingOpens := []
  pings := []
  nextPing := 0
  goneAway := false
  now
  lastRecv := now
  keepalive
  wake := none

/-- The entry has the stream id `id`. -/
def byId (id : Nat) (e : Entry) : Bool := e.id.val == id

/-- The entry has the key `k`. -/
def byKey (k : StreamKey) (e : Entry) : Bool := e.key == k

/-- The live stream with this id. -/
def find? (s : State) (id : Nat) : Option Entry :=
  s.streams.find? (byId id)

/-- The live streams the peer opened, for our side `role`. -/
def inboundCount (role : Role) (l : List Entry) : Nat :=
  l.countP fun e => e.id.opener != role

/-- Our live streams that the peer has not acknowledged. -/
def unackedCount (role : Role) (l : List Entry) : Nat :=
  l.countP fun e => e.id.opener == role && !e.state.acked

/-- Store the new state of entry `e` in place, or retire the entry when
both directions are closed (owned contract 3). -/
def put (s : State) (e : Entry) (st : StreamState) : State :=
  if st.live then
    { s with streams := s.streams.map fun x => if x.id = e.id then { e with state := st } else x }
  else { s with streams := s.streams.filter fun x => x.id ≠ e.id }

/-- Add a stream we open, at `nextLocal` and `nextEpoch`. The caller has
checked the id against the 32-bit field. -/
def addLocal (s : State) (hlt : s.nextLocal < streamIdLimit) : State :=
  { s with
    streams := ⟨⟨s.nextLocal, s.role, s.nextLocalParity, s.nextLocalPos, hlt⟩, s.nextEpoch,
      StreamState.fresh true⟩ :: s.streams
    nextLocal := s.nextLocal + 2
    nextLocalParity := by have := s.nextLocalParity; omega
    nextLocalPos := by omega
    nextEpoch := s.nextEpoch + 1 }

/-- Add stream `id`, which the peer opened, in state `st`, at
`nextEpoch`. A stream already closed both ways is not stored. -/
def addRemote (s : State) (id : StreamId) (st : StreamState) : State :=
  { s with
    streams := if st.live then ⟨id, s.nextEpoch, st⟩ :: s.streams else s.streams
    nextEpoch := s.nextEpoch + 1 }

end State

/-! ## Session events -/

/-- Open a stream now: SYN goes out. The ids run out at `2 ^ 32`. -/
def openNow (s : State) (tag : Nat) : State × Array Action :=
  if hlt : s.nextLocal < streamIdLimit then
    (s.addLocal hlt, #[.send (windowFrame synFlags s.nextLocal), .opened tag ⟨s.nextLocal, s.nextEpoch⟩])
  else (s, #[.openRefused tag .closed])

/-- Open the waiting requests while our ACK backlog has room. -/
def openPending (s : State) : List Nat → Array Action → State × Array Action
  | [], acts => ({ s with pendingOpens := [] }, acts)
  | tag :: rest, acts =>
    if State.unackedCount s.role s.streams < backlogCap then
      let (s', a) := openNow s tag
      openPending s' rest (acts ++ a)
    else ({ s with pendingOpens := tag :: rest }, acts)

/-- The application opens a stream. Beyond the ACK backlog (spec,
"Implementation considerations") the request waits for an ACK, in
order. -/
def onOpen (s : State) (tag : Nat) : State × Array Action :=
  if s.goneAway then (s, #[.openRefused tag .closed])
  else if s.pendingOpens.isEmpty && State.unackedCount s.role s.streams < backlogCap then
    openNow s tag
  else ({ s with pendingOpens := s.pendingOpens ++ [tag] }, #[])

/-- Run an entry operation on the first live stream that `p` picks, and
store the entry back. No such stream gives `missing`. A frame of the
peer picks its stream by the id (`byId`), and an event of the
application by the key (`byKey`). -/
def onEntry (s : State) (p : Entry → Bool) (f : Entry → StreamState × Array Action)
    (missing : Array Action) : State × Array Action :=
  match s.streams.find? p with
  | none => (s, missing)
  | some e =>
    let (st, acts) := f e
    (s.put e st, acts)

/-- We go away: the go-away frame goes out, and from now on no stream
opens on either side. The waiting opens are refused. -/
def onGoAway (s : State) : State × Array Action :=
  if s.goneAway then (s, #[])
  else
    ({ s with goneAway := true, pendingOpens := [] },
      #[.send (goAwayFrame .normal)] ++ (s.pendingOpens.map fun t => Action.openRefused t .closed).toArray)

/-- Send a ping: the application's under `tag`, or a keepalive under
`none`. The opaque value is our own counter, and the pong must arrive
within `pingDeadlineMs` of now. -/
def sendPing (s : State) (tag : Option Nat) : State × Array Action :=
  let value := s.nextPing % streamIdLimit
  ({ s with pings := s.pings ++ [⟨value, tag, s.now + pingDeadlineMs⟩], nextPing := s.nextPing + 1 },
    #[.send (frame .ping synFlags 0 value)])

/-- The application pings. -/
def onPing (s : State) (tag : Nat) : State × Array Action :=
  sendPing s (some tag)

/-- A keepalive ping is in flight. -/
def keepaliveOut (s : State) : Bool :=
  s.pings.any (·.tag.isNone)

/-- The clock reads `t` (module doc, "Time"). Pings past their due time
fail: the application's with `timeout`, and a keepalive ends the
session. Then, after a keepalive interval with no bytes from the peer,
a keepalive goes out. -/
def onTick (s : State) (t : Nat) : State × Array Action :=
  let s := { s with now := max s.now t }
  let (late, live) := s.pings.partition (·.due ≤ s.now)
  let failed : Array Action := (late.map fun p => match p.tag with
    | some tag => Action.refused tag .timeout
    | none => Action.expired).toArray
  let s := { s with pings := live }
  match s.keepalive with
  | some k =>
    if !keepaliveOut s && s.lastRecv + k ≤ s.now then
      let (s, ping) := sendPing s none
      (s, failed ++ ping)
    else (s, failed)
  | none => (s, failed)

/-- The next time the core needs a tick: the earliest due time of a
ping, and the end of the keepalive interval while no keepalive is in
flight. -/
def nextDeadline (s : State) : Option Nat :=
  let pingDue := s.pings.foldl (fun m p => some (match m with | some d => min d p.due | none => p.due)) none
  let keepDue := match s.keepalive with
    | some k => if keepaliveOut s then none else some (s.lastRecv + k)
    | none => none
  match pingDue, keepDue with
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- Ask for a tick at the next deadline, when it changed. -/
def schedule (s : State) (acts : Array Action) : State × Array Action :=
  let next := nextDeadline s
  if next == s.wake then (s, acts)
  else
    let s := { s with wake := next }
    match next with
    | some t => (s, acts.push (.wakeAt t))
    | none => (s, acts)

/-! ## Frames from the peer -/

/-- A ping frame. A SYN asks for the echo; an ACK answers our ping of
the same value. -/
def recvPing (s : State) (h : Header) : State × Array Action :=
  if h.flags.syn then (s, #[.control (frame .ping ackFlags 0 h.length)])
  else if h.flags.ack then
    match s.pings.find? (·.value == h.length) with
    | some p =>
      let s := { s with pings := s.pings.filter (·.value != h.length) }
      match p.tag with
      | some tag => (s, #[.done tag])
      | none => (s, #[])
    | none => (s, #[])
  else (s, #[])

/-- A go-away frame ends the session: a normal one as a shutdown, any
other as the peer's error. -/
def recvGoAway (s : State) (h : Header) : Except ProtocolError (State × Array Action) :=
  match GoAwayCode.ofCode? h.length with
  | some .normal => .ok (s, #[.shutdown])
  | some code => .error (.goAway code)
  | none => .error (.unknownGoAwayCode h.length)

/-- A data or window-update frame. Only a SYN with the peer's parity
creates a stream, and a SYN on any other id is `invalidStreamId`
(owned contract 2). A frame without SYN for an unknown id creates
nothing, and its payload passes by. -/
def recvStream (s : State) (h : Header) : Except ProtocolError (State × Array Action) :=
  let id := h.streamId
  let isData := h.type == .data
  let skip : Rx := if isData && h.length > 0 then .payload id h.length false false
    else .header ⟨.empty⟩
  -- No stream holds more than the initial window, so a longer data
  -- frame is an error whatever its id (§5.1).
  if isData && h.length > initialWindow then .error (.windowExceeded id h.length initialWindow)
  else if h.flags.syn then
    -- The boundary check of the id: the peer's parity, and not 0.
    match StreamId.ofRemote? s.role id h.streamIdLt with
    | none =>
      -- Not the peer's to open: id 0 is the session, and our parity is
      -- ours. The peer broke the protocol (`invalidStreamId`).
      .error (.invalidStreamId id)
    | some sid =>
      -- The peer numbers its own streams, and the spec asks no order of
      -- it: go-yamux takes an id first and sends its SYN later, so SYNs
      -- of concurrent opens arrive out of order. Like go-yamux and
      -- rust-yamux, the core opens any id of the peer's parity that is
      -- not live; parity alone keeps the two sides apart (the package
      -- ARCHITECTURE, "How this package reads two root rules"). The new stream
      -- gets a new epoch, so a handle of an earlier stream on the id
      -- cannot reach it (`StreamKey`).
      if (s.find? id).isSome then .error (.duplicateStream id)
      else if s.goneAway || maxIncomingStreams ≤ State.inboundCount s.role s.streams then
        -- The peer holds `maxIncomingStreams` live streams, or we went
        -- away: refuse with RST, the answer the spec demands for a SYN
        -- we do not accept.
        .ok ({ s with rx := skip }, #[.reply (windowFrame rstFlags id)])
      else
        match (⟨sid, s.nextEpoch, StreamState.fresh false⟩ : Entry).onFrame s.role h with
        | .error err => .error err
        | .ok (st, acts, rx) =>
          -- The ACK comes before the offer. When the accept queue is
          -- full, the shell resets the stream at the offer, and the wire
          -- then carries ACK, then RST: an accept, then a reset.
          let opened : Array Action :=
            if st.live then #[.reply (windowFrame ackFlags id), .accept ⟨id, s.nextEpoch⟩] else #[]
          .ok ({ s.addRemote sid st with rx }, opened ++ acts)
  else
    match s.find? id with
    | none => .ok ({ s with rx := skip }, #[])
    | some e =>
      match e.onFrame s.role h with
      | .error err => .error err
      | .ok (st, acts, rx) =>
        let s := { s.put e st with rx }
        -- An ACK frees a place in our backlog for a waiting open.
        if h.flags.ack then .ok (openPending s s.pendingOpens acts) else .ok (s, acts)

/-- A complete header: the frame by its type. -/
def recvHeader (s : State) (h : Header) : Except ProtocolError (State × Array Action) :=
  match h.type with
  | .data | .windowUpdate => recvStream s h
  | .ping => .ok (recvPing s h)
  | .goAway => recvGoAway s h

/-- A piece of a data payload. It reaches the stream only while the
stream still reads. -/
def recvChunk (s : State) (id : Nat) (chunk : ByteArray) (deliver : Bool) : State × Array Action :=
  if deliver && chunk.size > 0 then
    onEntry s (State.byId id) (fun e =>
      if e.state.recvOpen || e.state.eofDue then e.state.offer e.id.val chunk else (e.state, #[])) #[]
  else (s, #[])

/-- The end of a data payload: a FIN on its frame applies now. -/
def finishPayload (s : State) (id : Nat) (deliver fin : Bool) : State × Array Action :=
  if deliver && fin then onEntry s (State.byId id) (fun e => Entry.finRemote e.id.val e.state) #[]
  else (s, #[])

/-- Walk the bytes `b` from `pos`, frame by frame. `fuel` bounds the
passes: each pass takes at least one byte, so `b.size + 1` passes are
enough. -/
def recvBytes (fuel : Nat) (s : State) (b : ByteArray) (pos : Nat) (acts : Array Action) :
    Except ProtocolError (State × Array Action) :=
  match fuel with
  | 0 => .ok (s, acts)
  | fuel + 1 =>
    if b.size ≤ pos then .ok (s, acts)
    else
      match s.rx with
      | .header seen =>
        let need := headerSize - seen.bytes.size
        if pos + need ≤ b.size then
          match Header.decodeAt? (seen.bytes ++ b.extract pos (pos + need)) 0 with
          | .error _ => .error .malformedHeader
          | .ok h =>
            match recvHeader { s with rx := .header ⟨.empty⟩ } h with
            | .error e => .error e
            | .ok (s, a) => recvBytes fuel s b (pos + need) (acts ++ a)
        else .ok ({ s with rx := .header ⟨seen.bytes ++ b.extract pos b.size⟩ }, acts)
      | .payload id remaining deliver fin =>
        let n := min remaining (b.size - pos)
        let c := recvChunk s id (b.extract pos (pos + n)) deliver
        let acts := acts ++ c.2
        if remaining - n = 0 then
          let r := finishPayload c.1 id deliver fin
          recvBytes fuel { r.1 with rx := .header ⟨.empty⟩ } b (pos + n) (acts ++ r.2)
        else recvBytes fuel { c.1 with rx := .payload id (remaining - n) deliver fin } b (pos + n) acts

/-! ## The step -/

/-- The bytes of one read arrived at the latest tick: the shell ticks
right before each read (module doc, "Time"). Bytes from the peer
restart the keepalive interval. -/
def heard (s : State) (p : Blob) : State :=
  if p.bytes.isEmpty then s else { s with lastRecv := s.now }

/-- The transition function of a session. Only the bytes, a tick, and
our ping can move a deadline, so only those three ask for a new tick
(`schedule`). -/
def step (s : State) : Event → Except ProtocolError (State × List Action)
  | .bytes p =>
    (recvBytes (p.bytes.size + 1) (heard s p) p.bytes 0 #[]).map fun (s, a) =>
      let (s, a) := schedule s a; (s, a.toList)
  | .eof => .ok (s, [.shutdown])
  | .tick t => let (s, a) := onTick s t; let (s, a) := schedule s a; .ok (s, a.toList)
  | .openStream tag => let (s, a) := onOpen s tag; .ok (s, a.toList)
  | .write k tag p =>
    let (s, a) := onEntry s (State.byKey k) (·.write tag p) #[.refused tag .closed]; .ok (s, a.toList)
  | .consumed k n => let (s, a) := onEntry s (State.byKey k) (·.consume n) #[]; .ok (s, a.toList)
  | .close k => let (s, a) := onEntry s (State.byKey k) Entry.closeLocal #[]; .ok (s, a.toList)
  | .reset k => let (s, a) := onEntry s (State.byKey k) Entry.resetLocal #[]; .ok (s, a.toList)
  | .ping tag => let (s, a) := onPing s tag; let (s, a) := schedule s a; .ok (s, a.toList)
  | .goAway => let (s, a) := onGoAway s; .ok (s, a.toList)

/-! ## Examples

One `step` per case, on a new client session, with the frames written
out as wire bytes. A header is version, type, flags (two bytes), the
stream id (four bytes), and the length (four bytes), all big-endian.

`Except` has no `DecidableEq`, so an accepted step is stated through
`toOption`, and a rejection through `matches`, which gives a `Bool`.
`decide +kernel` checks each one in the kernel alone. The elaborator's
own reduction of `step` exhausts its heartbeats here, and the kernel
answers in milliseconds. `+kernel` trusts the kernel only, with no
compiler axiom, unlike `native_decide`. -/

-- We open stream 1, the first odd id: a window update with SYN and a
-- zero delta.
example : (step (State.new .client) (.openStream 7)).toOption.map (·.2) =
    some [.send ⟨ofNatList [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]⟩, .opened 7 ⟨1, 0⟩] := by
  decide +kernel

-- The peer opens stream 2 with a SYN data frame that carries `abc`. The
-- ACK goes out first, then the offer, then the bytes.
example : (step (State.new .client)
    (.bytes ⟨ofNatList [0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0x61, 0x62, 0x63]⟩)).toOption.map
      (·.2) =
    some [.reply ⟨ofNatList [0, 1, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0]⟩, .accept ⟨2, 0⟩,
      .deliver 2 ⟨ofNatList [0x61, 0x62, 0x63]⟩] := by
  decide +kernel

-- A write within the credit goes out as one data frame. The write is
-- done, and the credit left goes to the next parked writer.
example : ((step (State.new .client) (.openStream 7)).toOption.bind fun (s, _) =>
    (step s (.write ⟨1, 0⟩ 8 ⟨ofNatList [0x61, 0x62, 0x63]⟩)).toOption.map (·.2)) =
    some [.send ⟨ofNatList [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0x61, 0x62, 0x63]⟩, .done 8,
      .credit 1] := by
  decide +kernel

-- The peer's ping 42 gets its echo, with ACK in place of SYN.
example : (step (State.new .client)
    (.bytes ⟨ofNatList [0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0x2A]⟩)).toOption.map (·.2) =
    some [.control ⟨ofNatList [0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0x2A]⟩] := by
  decide +kernel

-- Five bytes of a header wait in the receive cursor for the other seven.
example : (step (State.new .client) (.bytes ⟨ofNatList [0, 1, 0, 1, 0]⟩)).toOption.map
    (·.1.rx) = some (.header ⟨ofNatList [0, 1, 0, 1, 0]⟩) := by
  decide +kernel

-- A SYN on stream 1 has the client's parity, so the peer may not open it.
example : (step (State.new .client)
    (.bytes ⟨ofNatList [0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]⟩) matches
      .error (.invalidStreamId 1)) = true := by
  decide +kernel

-- A data frame of 262145 bytes (`00 04 00 01`) exceeds the initial
-- window, and the core rejects it at the header.
example : (step (State.new .client)
    (.bytes ⟨ofNatList [0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, 1]⟩) matches
      .error (.windowExceeded 1 262145 262144)) = true := by
  decide +kernel

-- Version 1 is not yamux.
example : (step (State.new .client)
    (.bytes ⟨ofNatList [1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0]⟩) matches
      .error .malformedHeader) = true := by
  decide +kernel

end Yamux
