import Std.Data.HashMap
import Std.Data.HashSet
import Std.Async.UDP
import Conc
import Streams
import QuicNative
import Quic.Constants
import Quic.Error
import Quic.Address
import Quic.View

/-!
# The endpoint's loop

An endpoint holds every QUIC connection of one UDP socket. The state of
the connections is ngtcp2's, inside the shim's endpoint object
(`QuicNative`). This module is the shell around it (root ARCHITECTURE
§3.3): one loop task that alone calls the shim, one reader task that
reads the socket, and one ticker task that wakes the loop at the shim's
timers. `Quic/Endpoint.lean` starts the three; the views of
`Quic/View.lean` talk to the loop through its command queue.

## The loop

The loop parks on four sources at once (`Conc.select`):

* the datagrams of the reader, on a bounded queue (`datagramQueueCap`);
* the commands of the views: open a stream, write, return read credit,
  reset a stream, close a connection;
* the earliest timer of the shim, through the `Clock` seam;
* the close of a listener.

Each turn starts with the shim's packets, which the loop sends. Then
the loop parks. It hands what woke it to the shim and drains the
shim's events into the views.

The loop's own state is plain data, threaded through the recursion:
the table of connections, and for each the table of streams. No other
task reads it, so it needs no cell (PRINCIPLES 3.3).

## A new connection

The shim bounds new connections before any state exists for them
(`QuicNative`, "The bounds of new connections"), and answers the
clients past the bounds itself. For a client within them, the loop
asks the listener's caller (`Admitted`). A refusal goes back to the
shim, which sends CONNECTION_REFUSED and keeps nothing. An admission
opens the connection with the caller's check. The loop keeps the
caller's value until the connection reaches the accept queue. A caller
that reads a clock for its check reads it once per handshake, at the
handshake's start.

A stream the peer opened gives its stream credit back once it is over
and the application has accepted it, as quic-go's does
(`streams_map_incoming.go`, `deleteStream`). So the peer never has more
than `maxStreamsBidi` streams open or waiting in the accept queue. The
queue holds as many, so it never fills.

## The end

A connection ends by a close of ours, by the peer's close, by a timer,
by a stateless reset, or by a protocol error. The shim reports each as
its own event, and the loop maps it to one arm of `Quic.Error`; an
orderly close is no error. The loop then wakes every view that parks on
the connection: the inboxes and the accept queue close, and every
write, open, and dial that waits gets its answer (PRINCIPLES 3.1). The
loop releases the admission of a connection that never reached the
accept queue. A dialing endpoint ends with its one connection. A
listening endpoint ends once its listener is closed and its last
connection has ended. The listener's close refuses the connections
still in their handshake with CONNECTION_REFUSED (RFC 9000 §20.1).
They are unauthenticated, and root §5.5 closes such connections at a
shutdown. So a closing host waits for no handshake.

At its end the loop wakes the reader with an empty datagram to the
socket itself. The reader's park then ends through libuv's own
callback, and the owner joins the three tasks (PRINCIPLES 3.2). The
socket closes with its last reference. In Lean v4.34, a cancelled
receive keeps libuv's reference to the socket, and the socket would
stay open for the life of the process (`stopReading`).
-/

set_option autoImplicit false

namespace Quic

open Conc Streams Multiformats

/-- The loop's state of one stream. -/
structure StreamState where
  inbox : Chan Item
  /-- The writes that wait for the peer's acknowledgments. -/
  waiting : Array (Chan (Except Streams.Error Unit)) := #[]
  /-- The peer's STOP_SENDING ended our writes. -/
  stopped : Bool := false
  /-- The peer opened the stream. -/
  remote : Bool := false

/-- The loop's state of one connection. `α` is the type of the
listener caller's value (`Admitted`). -/
structure ConnState (α : Type) where
  ports : ConnPorts
  streams : Std.HashMap UInt64 StreamState := {}
  /-- The peer's streams that the application has not accepted yet. -/
  unaccepted : Std.HashSet UInt64 := {}
  /-- The peer's streams that are over but not accepted yet: their
  credit returns at the accept (the module doc, "A new connection"). -/
  closedUnaccepted : Std.HashSet UInt64 := {}
  /-- The opens that wait for the peer's credit. -/
  opens : Array (Chan (Except Error Stream)) := #[]
  /-- A dial's answer slot, until the handshake ends. -/
  ready : Option (Chan (Except Error Conn)) := none
  /-- A server connection's admission, until the accept queue takes the
  connection; released at the end otherwise. -/
  admitted : Option (Admitted α) := none

/-- The promise of one receive on the socket: libuv resolves it with a
datagram or a fault. -/
abbrev RecvPromise :=
  IO.Promise (Except IO.Error (ByteArray × Option Std.Net.SocketAddress))

/-- The reader's park (`stopReading`). The loop's end sets `stopped`
and wakes a parked receive with a datagram to the socket itself. When
that send fails, it sets `fallback` and resolves the parked receive
itself. libuv drops a cancelled promise, and a task parked on it would
never wake (the TCP transport's rule, `Streams/Tcp.lean`; PRINCIPLES
3.1). -/
structure ReadState where
  /-- The loop has ended: no receive starts. -/
  stopped : Bool := false
  -- TODO(lean v4.36): remove with the workaround (the package
  -- ARCHITECTURE, "Workaround: the UDP cancel of Lean v4.34").
  /-- The wake datagram could not be sent: a receive that starts after
  the stop resolves its own promise. -/
  fallback : Bool := false
  /-- The promise of the parked receive, when one is parked. -/
  parked : Option RecvPromise := none

/-- The shared parts of an endpoint. -/
structure Shared (α : Type) where
  native : QuicNative.Endpoint
  socket : Std.Async.UDP.Socket
  -- TODO(lean v4.36): remove with the workaround (`stopReading`).
  /-- Where the socket receives its own datagram (`selfAddress`). -/
  selfAddr : Std.Net.SocketAddress
  clock : Clock
  localAddr : Multiaddr
  /-- The listener caller's admission of each new connection, by our
  address and the peer's (the module doc, "A new connection"). -/
  admit : (localAddr remoteAddr : Multiaddr) → BaseIO (Option (Admitted α))
  /-- The datagrams of the reader: the bytes and the source. -/
  datagrams : Chan (ByteArray × ByteArray)
  /-- The commands of the views. Unbounded, the named exception of root
  §4.1. Each view posts one command and parks on its answer, or posts
  the credit of bytes it took. So the views and the window bound the
  posts. -/
  commands : Chan Command
  /-- Closed by a listener's `close`. -/
  stopAccepting : Chan Unit
  /-- The reader's park, which the loop's end must reach (`reader`). -/
  reading : OnceRef ReadState
  /-- The accept queue of a listening endpoint: each connection with the
  caller's value. -/
  listener : Option (Chan (Conn × α))
  /-- The wake at the shim's earliest timer (`Conc.Alarm`, root §3.3): it
  arms one timer per due time, so a turn that leaves the due time as it
  was arms none. -/
  alarm : Alarm
  /-- The ticks of the alarm, for the loop. One slot: a tick that waits
  already wakes the loop. -/
  ticks : Chan Unit
  /-- The loop, the reader, and the ticker. -/
  tasks : TaskSet

/-- The loop's state. -/
structure LoopState (α : Type) where
  conns : Std.HashMap UInt64 (ConnState α) := {}
  accepting : Bool
  /-- The due time the loop gave the alarm last, in the clock's
  milliseconds; `none` once a tick served it. -/
  due : Option Nat := none

/-- What woke the loop. -/
inductive Wake where
  | datagram (d : Option (ByteArray × ByteArray))
  | command (c : Option Command)
  | timer
  | stopAccepting

-- The type of the listener caller's value, in every step below. An
-- inductive would take it as a parameter too, so `Wake` comes first.
variable {α : Type}

/-! ## The loop's steps -/

/-- The multiaddr of the shim's address bytes; our own address when the
bytes name none (a connection that is gone). -/
def remoteOf (sh : Shared α) (b : ByteArray) : Multiaddr :=
  ((ofShim? b).bind multiaddrOf).getD sh.localAddr

/-- A fresh connection state. -/
def newConn : BaseIO (ConnState α) := do
  return { ports := ← ConnPorts.new }

/-- The text of an end event's reason. The bytes may be the peer's
CONNECTION_CLOSE reason, and no rule makes that UTF-8. The shim also
cuts a long reason at a byte count, which can split a character. So
the text drops up to three trailing bytes of a split character. A
reason that is still no UTF-8 becomes a placeholder, so the peer's
bytes never make a decode panic. -/
def reasonText (b : ByteArray) : String :=
  -- A trim never empties a reason that has bytes.
  let cut : List Nat := [0, 1, 2, 3].filter fun k => k == 0 || k < b.size
  match cut.findSome? fun k => String.fromUTF8? (b.extract 0 (b.size - k)) with
  | some t => t
  | none => s!"(a reason of {b.size} bytes that is no UTF-8)"

/-- The answer of an ended connection, by the end event of the shim
(`QuicNative.EventKind`). `none` is an orderly end. -/
def endOf (kind : QuicNative.EventKind) (code : UInt64) (detail : String) : Option Error :=
  match kind with
  | .connClosed => if code == orderlyClose then none else some (.closed code detail)
  | .connRefused => some (.refused detail)
  | .connFailed => some (.failed code detail)
  | .peerFailed => some (.peerFailed code detail)
  | .connTimeout => some .timeout
  | .connIdle => some .idle
  | .connDropped => some (.dropped detail)
  | _ => none

/-- An orderly close of either side is no error. -/
example : endOf .connClosed orderlyClose "" = none := rfl

/-- A refused certificate keeps its reason. -/
example : endOf .connRefused 0x12a "expired" = some (.refused "expired") := rfl

/-- End a connection: record how, release an admission the accept queue
never took, and wake every view (the module doc, "The end"). -/
def endConn (c : ConnState α) (e : Option Error) : BaseIO Unit := do
  c.ports.result.update fun | none => e | old => old
  if let some a := c.admitted then a.release
  if let some r := c.ready then
    discard <| r.trySend (.error (e.getD endedError))
  for (_, s) in c.streams.toList do
    s.inbox.close
    for w in s.waiting do discard <| w.trySend (.error .closed)
  for o in c.opens do discard <| o.trySend (.error (e.getD endedError))
  c.ports.accepts.close
  c.ports.ended.close

/-- A new stream of `conn` in the loop's tables, and its view. The inbox
is unbounded, the named exception of root §4.1: the peer cannot send
past the window we granted, so the window bounds it (`Quic/View.lean`,
"The streams"). -/
def addStream (sh : Shared α) (st : LoopState α) (conn sid : UInt64) (c : ConnState α)
    (remote : Bool := false) : BaseIO (Stream × LoopState α) := do
  let inbox ← Chan.newUnbounded
  let s ← mkStream sh.commands conn sid inbox
  let c := { c with streams := c.streams.insert sid { inbox, remote } }
  return (s, { st with conns := st.conns.insert conn c })

/-- The state of `conn` with the stream `sid` replaced by `s`. -/
def withStream (st : LoopState α) (conn sid : UInt64) (c : ConnState α) (s : StreamState) :
    LoopState α :=
  { st with conns := st.conns.insert conn { c with streams := c.streams.insert sid s } }

/-- Try the opens that wait for credit, in order. -/
def retryOpens (sh : Shared α) (st : LoopState α) (conn : UInt64) : IO (LoopState α) := do
  let some c := st.conns.get? conn | return st
  let mut st := { st with conns := st.conns.insert conn { c with opens := #[] } }
  let mut left : Array (Chan (Except Error Stream)) := #[]
  for o in c.opens do
    if !left.isEmpty then left := left.push o; continue
    let sid ← QuicNative.openStream sh.native conn
    if sid == QuicNative.openBlocked then left := left.push o
    else if sid == QuicNative.openGone then discard <| o.trySend (.error endedError)
    else
      let some c' := st.conns.get? conn | break
      let (s, st') ← addStream sh st conn sid c'
      st := st'
      discard <| o.trySend (.ok s)
  if let some c' := st.conns.get? conn then
    st := { st with conns := st.conns.insert conn { c' with opens := c'.opens ++ left } }
  return st

/-- Hand a finished server handshake to the listener, with the caller's
value. The answer is `true` when the accept queue took it. A full
queue, or a closed listener, refuses the connection with
CONNECTION_REFUSED, as quic-go's server does (`listenBacklog`). -/
def offer (sh : Shared α) (st : LoopState α) (conn : Conn) (value : α) : IO Bool := do
  let taken ← match sh.listener with
    | some l => if st.accepting then l.trySend (conn, value) else pure false
    | none => pure false
  unless taken do
    QuicNative.close sh.native conn.handle true connectionRefused "the accept queue is full"
      (← sh.clock.nowMs).toUInt64
  return taken

/-- The connection view of a finished handshake. -/
def connView (sh : Shared α) (handle : UInt64) (c : ConnState α) (cert : ByteArray)
    (owned : Bool) : IO Conn := do
  let alpn ← QuicNative.alpn sh.native handle
  let remote := remoteOf sh (← QuicNative.remote sh.native handle)
  return mkConn sh.commands (if owned then some sh.tasks else none) sh.localAddr handle c.ports
    cert alpn remote

/-- Handle one event of the shim. An event names a connection that the
loop holds: a dial's, or a server connection that `onDatagram` made. -/
def onEvent (sh : Shared α) (st : LoopState α) (ev : QuicNative.EventRaw) : IO (LoopState α) := do
  let some kind := QuicNative.EventKind.ofCode? ev.kind | return st
  let some c := st.conns.get? ev.conn | return st
  match kind with
  | .handshakeDone =>
    match c.ready, c.admitted with
    | some r, _ =>
      -- A dial: the dialer receives the connection.
      discard <| r.trySend (.ok (← connView sh ev.conn c ev.data true))
      return { st with conns := st.conns.insert ev.conn { c with ready := none } }
    | none, some a =>
      -- A peer dialed us: the listener receives the connection, and with
      -- it the caller's value.
      if ← offer sh st (← connView sh ev.conn c ev.data false) a.value then
        return { st with conns := st.conns.insert ev.conn { c with admitted := none } }
      return st
    | none, none => return st
  | .streamOpened =>
    let (s, st) ← addStream sh st ev.conn ev.stream c (remote := true)
    if ← c.ports.accepts.trySend (ev.stream, s) then
      let some c' := st.conns.get? ev.conn | return st
      return { st with
        conns := st.conns.insert ev.conn { c' with unaccepted := c'.unaccepted.insert ev.stream } }
    -- The credit rule keeps the queue from filling: a peer has at most
    -- `maxStreamsBidi` streams that are open or unaccepted. A full queue
    -- would be a bug, so the stream is refused, never lost.
    QuicNative.streamReset sh.native ev.conn ev.stream streamResetCode
    return st
  | .streamData =>
    if let some s := c.streams.get? ev.stream then
      if ev.data.size > 0 then discard <| s.inbox.trySend (.data ev.data)
      if ev.code == QuicNative.dataFin then discard <| s.inbox.trySend .fin
    return st
  | .streamReset =>
    -- The peer's sending part is over: our reads end after the bytes
    -- that came before it.
    if let some s := c.streams.get? ev.stream then
      discard <| s.inbox.trySend .reset
    return st
  | .streamStopped =>
    -- The peer reads no more: our writes end, and our reads go on.
    if let some s := c.streams.get? ev.stream then
      for w in s.waiting do discard <| w.trySend (.error .reset)
      return withStream st ev.conn ev.stream c { s with waiting := #[], stopped := true }
    return st
  | .streamClosed =>
    if let some s := c.streams.get? ev.stream then
      -- Every byte is acknowledged, or the stream was reset; the inbox
      -- keeps what the reader has not taken.
      for w in s.waiting do discard <| w.trySend (.ok ())
      s.inbox.close
      let c := { c with streams := c.streams.erase ev.stream }
      -- A stream of the peer's gives its credit back once it is over and
      -- accepted, as quic-go's does (the module doc, "A new connection").
      let c ← if !s.remote then pure c
        else if c.unaccepted.contains ev.stream then
          pure { c with closedUnaccepted := c.closedUnaccepted.insert ev.stream }
        else do
          QuicNative.grantStream sh.native ev.conn
          pure c
      return { st with conns := st.conns.insert ev.conn c }
    return st
  | .streamAcked =>
    if let some s := c.streams.get? ev.stream then
      if ev.code.toNat ≤ streamSendCap then
        for w in s.waiting do discard <| w.trySend (.ok ())
        return withStream st ev.conn ev.stream c { s with waiting := #[] }
    return st
  | .openCredit => retryOpens sh st ev.conn
  | .connClosed | .connRefused | .connFailed | .peerFailed | .connTimeout | .connIdle
  | .connDropped =>
    endConn c (endOf kind ev.code (reasonText ev.data))
    return { st with conns := st.conns.erase ev.conn }

/-- Drain the shim's events. The function is `partial`: it ends when
the queue is empty, and the shim adds no event while the loop drains. -/
partial def drainEvents (sh : Shared α) (st : LoopState α) : IO (LoopState α) := do
  match ← QuicNative.nextEvent sh.native with
  | none => return st
  | some ev => drainEvents sh (← onEvent sh st ev)

/-- Send the shim's datagrams. A send fault drops the datagram: QUIC
recovers a lost one. The function is `partial`, as `drainEvents` is. -/
partial def sendPackets (sh : Shared α) : Async Unit := do
  match ← (QuicNative.nextPacket sh.native : IO (Option (ByteArray × ByteArray))) with
  | none => return
  | some (bytes, dst) =>
    if let some sa := ofShim? dst then
      try sh.socket.send bytes (some sa) catch _ => pure ()
    sendPackets sh

/-- Our reset of a stream (`Quic/View.lean`, "The streams"). Both
directions end. The loop drops the bytes that wait in the inbox and
returns their credit to the peer. The reader sees `.reset` at once,
and every write that waits answers `.reset`. -/
def resetStream (sh : Shared α) (st : LoopState α) (conn sid : UInt64) : IO (LoopState α) := do
  QuicNative.streamReset sh.native conn sid streamResetCode
  let some c := st.conns.get? conn | return st
  let some s := c.streams.get? sid | return st
  let dropped ← s.inbox.drain
  let bytes := dropped.foldl (fun n i => match i with | .data b => n + b.size | _ => n) 0
  if bytes > 0 then QuicNative.streamConsume sh.native conn sid bytes.toUInt64
  discard <| s.inbox.trySend .reset
  for w in s.waiting do discard <| w.trySend (.error .reset)
  return withStream st conn sid c { s with waiting := #[], stopped := true }

/-- Handle one command of a view. -/
def onCommand (sh : Shared α) (st : LoopState α) (cmd : Command) : IO (LoopState α) := do
  let now := (← sh.clock.nowMs).toUInt64
  match cmd with
  | .openStream conn reply =>
    let some c := st.conns.get? conn
      | discard <| reply.trySend (.error endedError); return st
    let sid ← QuicNative.openStream sh.native conn
    if sid == QuicNative.openBlocked then
      return { st with conns := st.conns.insert conn { c with opens := c.opens.push reply } }
    if sid == QuicNative.openGone then
      discard <| reply.trySend (.error endedError)
      return st
    let (s, st) ← addStream sh st conn sid c
    discard <| reply.trySend (.ok s)
    return st
  | .write conn sid bytes fin reply =>
    let some c := st.conns.get? conn | discard <| reply.trySend (.error .closed); return st
    let some s := c.streams.get? sid | discard <| reply.trySend (.error .closed); return st
    if s.stopped then
      discard <| reply.trySend (.error .reset)
      return st
    let n ← QuicNative.streamWrite sh.native conn sid bytes fin
    if n == QuicNative.writeRefused then
      discard <| reply.trySend (.error .closed)
      return st
    if n.toNat ≤ streamSendCap then
      discard <| reply.trySend (.ok ())
      return st
    -- Past the cap: the write waits for the peer's acknowledgments.
    return withStream st conn sid c { s with waiting := s.waiting.push reply }
  | .consume conn sid n =>
    QuicNative.streamConsume sh.native conn sid n
    return st
  | .reset conn sid => resetStream sh st conn sid
  | .accepted conn sid =>
    let some c := st.conns.get? conn | return st
    let c := { c with unaccepted := c.unaccepted.erase sid }
    if c.closedUnaccepted.contains sid then
      QuicNative.grantStream sh.native conn
      return { st with
        conns := st.conns.insert conn { c with closedUnaccepted := c.closedUnaccepted.erase sid } }
    return { st with conns := st.conns.insert conn c }
  | .close conn code reason =>
    if st.conns.contains conn then
      QuicNative.close sh.native conn false code reason now
    return st

/-- Take one datagram. A datagram that would open a new connection
within the shim's bounds goes to the caller's admission (the module
doc, "A new connection"). A refusal sends CONNECTION_REFUSED. An
admission opens the connection with its check, and the loop keeps the
admission in its table. -/
def onDatagram (sh : Shared α) (st : LoopState α) (bytes src : ByteArray) (now : UInt64) :
    IO (LoopState α) := do
  unless ← QuicNative.recv sh.native bytes src now do return st
  match ← sh.admit sh.localAddr (remoteOf sh src) with
  | none =>
    QuicNative.refuse sh.native bytes src now
    return st
  | some a =>
    let handle ← QuicNative.accept sh.native bytes src now a.check
    if handle == 0 then
      a.release
      return st
    -- The ascription names `α`: the update reads no field that fixes it.
    let fresh ← (newConn : BaseIO (ConnState α))
    let c := { fresh with admitted := some a }
    return { st with conns := st.conns.insert handle c }

/-- The loop is over: no connection is left, and none can come. -/
def finished (st : LoopState α) : Bool :=
  !st.accepting && st.conns.isEmpty

/-- The fault that a stopped receive answers. -/
def stoppedError : IO.Error :=
  .resourceVanished 0 "quic: the endpoint has ended"

/-- Stop the reader. The stop marks `stopped`, then sends an empty
datagram to the socket itself. The parked receive ends through libuv's
own callback, which drops libuv's reference to the socket, so the
socket closes with its last Lean reference. A receive that starts after
the stop takes the datagram from the socket's buffer, so the wake
cannot be lost. The datagram works around a bug of Lean v4.34: its
`cancelRecv` keeps that reference, and the socket would stay open for
the life of the process (the package ARCHITECTURE, "Workaround: the
UDP cancel of Lean v4.34").

When the send fails, the stop takes the fallback path: it marks
`fallback`, resolves the parked receive itself, and cancels it. The
reader ends, and this one socket stays open. -/
-- TODO(lean v4.36): drop the datagram, and keep the fallback path as
-- the only one.
def stopReading (sh : Shared α) : Async Unit := do
  sh.reading.update fun s => { s with stopped := true }
  try sh.socket.send .empty (some sh.selfAddr)
  catch _ =>
    -- One atomic step takes the park, so the reader either registered
    -- it before (the stop resolves it) or finds `fallback` after.
    let parked ← (sh.reading.updateGet fun s => (s.parked, { s with fallback := true, parked := none }) :
      BaseIO (Option RecvPromise))
    if let some p := parked then p.resolve (.error stoppedError)
    discard sh.socket.native.cancelRecv.toBaseIO

/-- Close what the loop leaves: the reader's park, and the queues of
the views, answering every command that still waits. -/
def finish (sh : Shared α) (st : LoopState α) : Async Unit := do
  stopReading sh
  -- A reader that parks on a full queue wakes with the close, and so
  -- does the ticker, at its alarm and at its tick.
  sh.datagrams.close
  sh.alarm.close
  sh.ticks.close
  sh.commands.close
  for cmd in ← sh.commands.drain do
    match cmd with
    | .openStream _ r => discard <| r.trySend (.error endedError)
    | .write _ _ _ _ r => discard <| r.trySend (.error .closed)
    | _ => pure ()
  for (_, c) in st.conns.toList do endConn c (some endedError)
  if let some l := sh.listener then l.close

/-- The loop (the module doc, "The loop"). The function is `partial`:
it ends when the endpoint has no connection and can get none. No
measure shows that a peer ever ends a connection (CLAUDE.md, "`partial
def`"). -/
partial def loop (sh : Shared α) (st : LoopState α) : Async Unit := do
  -- Each turn starts with the shim's output: a dial's first packet goes
  -- out here, before the shim has any timer to wake the loop.
  QuicNative.flush sh.native (← (sh.clock.nowMs : BaseIO Nat)).toUInt64
  sendPackets sh
  -- The flush can end a connection: its events come now.
  let st ← drainEvents sh st
  if finished st then
    finish sh st
    return
  -- The alarm learns the shim's earliest timer only when it changes, so
  -- a turn that leaves it as it was arms no timer. With no timer set,
  -- the loop wakes on its queues alone: a connection always has its
  -- idle timer, so an endpoint with none has nothing to time.
  let due ← (QuicNative.expiry sh.native : IO UInt64)
  let st ← if due != QuicNative.noExpiry && st.due != some due.toNat then do
      (sh.alarm.set due.toNat : BaseIO Unit)
      pure { st with due := some due.toNat }
    else pure st
  -- Park: a datagram, a command, the alarm's tick, or a listener's close
  -- wakes it. The end of a connection comes as a datagram, a command, or
  -- a tick, so every end reaches the loop. A closed `stopAccepting`
  -- answers every receive at once, so the loop parks on it only while
  -- it still accepts. Past that, the park would wake every turn, and the
  -- loop would spin until its last connection ends.
  let datagram := Park.recv sh.datagrams Wake.datagram
  let command := Park.recv sh.commands Wake.command
  let timed := Park.recv sh.ticks fun _ => Wake.timer
  let wake ← if st.accepting then
      select #[datagram, command, timed,
        Park.recv sh.stopAccepting fun _ => Wake.stopAccepting]
    else select #[datagram, command, timed]
  let now := (← (sh.clock.nowMs : BaseIO Nat)).toUInt64
  let st ← match wake with
    | .datagram (some (bytes, src)) => onDatagram sh st bytes src now
    | .datagram none => pure st
    | .command (some cmd) => onCommand sh st cmd
    | .command none => pure st
    | .timer => do
      QuicNative.expire sh.native now
      -- The tick served the due time: the next turn sets the alarm
      -- again, even to the same time.
      pure { st with due := none }
    | .stopAccepting => do
      -- The listener's close: no connection comes after it, and the
      -- ones still in their handshake end now (the module doc, "The
      -- end").
      if let some l := sh.listener then l.close
      QuicNative.refusePending sh.native connectionRefused "the listener has closed" now
      pure { st with accepting := false }
  let st ← drainEvents sh st
  loop sh st

/-- Wait for a native promise. A promise that libuv drops unresolved
answers a fault; `stopReading` makes sure no promise that the reader
waits on is dropped that way. -/
def awaitRecv (p : RecvPromise) :
    Async (Except IO.Error (ByteArray × Option Std.Net.SocketAddress)) :=
  try .ok <$> Std.Async.Async.ofPromise (pure p)
  catch e => pure (.error e)

/-- The reader: each datagram of the socket goes to the loop. It parks
on the native receive, as the TCP transport's read does, and holds no
thread while it waits. `Std`'s receive selector would wait on the
receive with `.block` once the socket is readable, which holds a pool
thread for each datagram (the package ARCHITECTURE, "Decisions"). The
function is `partial`, as the read loops of `net/streams` are. It ends
at the loop's end, which wakes the parked receive (`stopReading`). A
socket fault ends it too, and the connections then end by their idle
timers. -/
partial def reader (sh : Shared α) : Async Unit := do
  if (← (sh.reading.get : BaseIO ReadState)).stopped then return
  let p ← sh.socket.native.recv maxDatagram.toUInt64
  -- Register the park, unless the stop has fallen back; then the reader
  -- resolves its own promise, as the stop would have. After a stop
  -- that sent its wake datagram, the receive takes that datagram.
  -- TODO(lean v4.36): with the workaround gone, every stop resolves the
  -- promise, so the test of `fallback` goes too.
  let parked ← (sh.reading.updateGet fun s =>
    if s.fallback then (false, s) else (true, { s with parked := some p }) : BaseIO Bool)
  if !parked then
    p.resolve (.error stoppedError)
    discard sh.socket.native.cancelRecv.toBaseIO
  -- Park: libuv resolves the promise with a datagram or a fault. The
  -- loop's end sends the datagram that wakes it, or resolves it with
  -- `stoppedError` when that send fails.
  let r ← awaitRecv p
  sh.reading.update fun s => { s with parked := none }
  -- The stop's wake, or a datagram that came with it: the loop has
  -- ended, and no one takes it.
  if (← (sh.reading.get : BaseIO ReadState)).stopped then return
  match r with
  | .error _ => return
  | .ok (bytes, some src) =>
    -- Park: the loop takes the datagram, and its end closes the queue.
    match ← sh.datagrams.send (bytes, toShim src) with
    | .ok () => reader sh
    | .error _ => return
  | .ok (_, none) => reader sh

/-- The ticker: it posts a tick at each due time the loop asked for
(`Conc.Alarm`). It ends when the loop's end closes the alarm or the
tick queue. -/
def ticker (sh : Shared α) : Async Unit :=
  sh.alarm.run sh.clock fun _ => sh.ticks.send ()

end Quic
