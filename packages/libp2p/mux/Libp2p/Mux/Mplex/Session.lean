import Libp2p.Core.Mux
import Libp2p.Mux.Mplex.Wire
import Libp2p.Mux.Mplex.State
import Conc
import Streams

/-!
# The mplex session shell

One session runs two tasks over one `Connection`, and a `TaskSet`
owns both (ARCHITECTURE §4.1, rule 2):

* **The reader** decodes messages off the connection with
  `Wire.decodeAtB?` and applies each one to the stream table. It is
  the one task that reads the connection.
* **The writer** takes work off the outbound queue, in order, and is
  the one task that writes the connection. Every local stream
  operation goes through it, so a close always follows the writes
  queued before it, and a write queued after a close is refused.

The table lives in one `OnceRef`, and every change is one
`updateGet` with a pure transition of `Mplex/State.lean` (§4.1,
rule 3).

## Where the tasks park

The reader parks on three things: `Connection.read`, the inbox of a
stream, and the accept queue. The session close wakes all three: it
closes every inbox, the accept queue, and the connection. A local
reset of a stream closes that inbox too. The reader never parks on the
writer: the one message it sends, the reset of an inbound open over
`liveStreamCap`, goes through `trySend`, and a full queue drops it.
So a peer that does not read cannot stop our reads.

mplex has no flow control (the spec, "Implementation notes"). A stream
whose inbox is full blocks the reader until the application reads,
resets the stream, or closes the session. This is the first of the two
answers the spec allows. TCP then slows the peer. go-mplex waits 5
seconds and resets the stream instead; the difference is recorded in
the package ARCHITECTURE.

## Session end

The reader ends at the end of the connection, at a read fault, or at a
protocol error. Its teardown records the answer in the `Outcome`,
ends every stream, closes the queues, and closes the connection. A
stream whose peer direction was still open reads `.error .closed`
once; a write after the end answers `.error .closed`.
-/

set_option autoImplicit false

namespace Libp2p.Mux.Mplex.Session

open Libp2p.Core
open Libp2p.Mux.Mplex.Wire
open Libp2p.Mux.Mplex.State
open Conc hiding Error

/-- The chunks one stream inbox holds. A chunk is one message, at most
`mplexMessageCap` bytes. -/
def inboxCap : Nat := 8

/-- The inbound streams that wait for `accept`. go-mplex uses 16. -/
def acceptCap : Nat := 16

/-- The work items that wait for the writer. -/
def outboundCap : Nat := 64

/-! ## Ports -/

/-- The runtime side of one stream. -/
structure Port where
  /-- The data the reader delivered, in order. A close ends it. -/
  inbox : Chan ByteArray
  /-- How the stream ended abnormally, and whether a read has reported
  it. The first cause stays. -/
  fate : OnceRef (Option Streams.Error × Bool)

/-- What the next read of a stream does. -/
private inductive ReadStep where
  /-- Read the inbox. -/
  | live
  /-- Report the error, once. -/
  | report (e : Streams.Error)
  /-- The stream is dead after its error: the end of the stream. -/
  | dead

namespace Port

/-- A port for a new stream. -/
def new : BaseIO Port :=
  return { inbox := ← Chan.new inboxCap, fate := ← OnceRef.new (none, false) }

/-- End the stream with `e`, unless it has a cause already, and wake
every task parked on its inbox. -/
def abort (p : Port) (e : Streams.Error) : BaseIO Unit := do
  p.fate.update fun (f, r) => (f.or (some e), r)
  p.inbox.close

/-- The cause of an abnormal end, if any. -/
def cause (p : Port) : BaseIO (Option Streams.Error) :=
  return (← p.fate.get).1

/-- The step of a read: one atomic look at the fate, which marks the
error reported the first time. -/
private def readStep (p : Port) : BaseIO ReadStep :=
  p.fate.updateGet fun
    | (some e, false) => (.report e, (some e, true))
    | (some e, true) => (.dead, (some e, true))
    | (none, r) => (.live, (none, r))

end Port

/-! ## The runtime -/

/-- The answer slot of one stream operation. -/
private abbrev Reply := Chan (Except Streams.Error Unit)

/-- Work for the writer. -/
private inductive Out where
  /-- Encoded bytes: an open or a reset. -/
  | raw (bytes : ByteArray) (reply : Option Reply)
  /-- A stream write. The writer checks the local direction first. -/
  | data (key : Key) (port : Port) (bytes : ByteArray) (reply : Reply)
  /-- A stream close. The writer ends the local direction. -/
  | close (key : Key) (reply : Reply)

/-- The shared state of one session. -/
private structure Runtime where
  conn : Streams.Connection
  table : OnceRef (Table Port)
  accepts : Chan Streams.Stream
  out : Chan Out
  outcome : Outcome Core.Error
  tasks : TaskSet

/-- Answer a reply slot, if there is one. -/
private def answer (reply : Option Reply) (r : Except Streams.Error Unit) : BaseIO Unit := do
  if let some c := reply then discard <| c.trySend r

/-- Queue work for the writer, and park until it answers.
`.error .closed` once the session has ended. -/
private def submit (rt : Runtime) (mk : Reply → Out) : Async (Except Streams.Error Unit) := do
  let reply : Reply ← Chan.new 1
  match ← rt.out.send (mk reply) with
  | .error _ => return .error .closed
  | .ok () =>
    -- Park: the writer answers every item it takes, and it takes every
    -- item the queue holds before it ends.
    match ← reply.recv with
    | some r => return r
    | none => return .error .closed

/-- The stream view of one table entry. -/
private def streamOf (rt : Runtime) (key : Key) (port : Port) : Streams.Stream where
  read := do
    match ← (port.readStep : BaseIO ReadStep) with
    | .report e => return .error e
    | .dead => return .ok none
    | .live =>
      -- Park: the reader's delivery wakes it, and so does any end of
      -- the stream, which closes the inbox.
      match ← port.inbox.recv with
      | some chunk => return .ok (some chunk)
      | none =>
        match ← (port.readStep : BaseIO ReadStep) with
        | .report e => return .error e
        | _ => return .ok none
  write := fun bytes => submit rt (.data key port bytes)
  close := discard <| submit rt (.close key)
  reset := do
    let due ← (rt.table.updateGet (Table.resetLocal key) : BaseIO Bool)
    port.abort .reset
    if due then
      discard <| submit rt fun reply =>
        .raw (encodeB (resetFlag key) key.id .empty) (some reply)

/-! ## The writer -/

/-- Write bytes to the connection. A fault ends the session: the
writer records it and closes the connection, which wakes the reader. -/
private def put (rt : Runtime) (bytes : ByteArray) : Async (Except Streams.Error Unit) := do
  try
    rt.conn.write bytes
    return .ok ()
  catch e =>
    rt.outcome.recordFault e
    rt.conn.close
    return .error .closed

/-- Write `bytes` as data messages of at most `mplexMessageCap` bytes
each. The spec allows "up to 1MiB per message". -/
private def putData (rt : Runtime) (key : Key) (bytes : ByteArray) :
    Async (Except Streams.Error Unit) := do
  let cap := Libp2p.Mux.mplexMessageCap
  let count := (bytes.size + cap - 1) / cap
  for i in [0:count] do
    let chunk := bytes.extract (i * cap) ((i + 1) * cap)
    if let .error e ← put rt (encodeB (dataFlag key) key.id chunk) then return .error e
  return .ok ()

/-- Apply one work item. -/
private def perform (rt : Runtime) : Out → Async Unit
  | .raw bytes reply => do
    let r ← put rt bytes
    answer reply r
  | .data key port bytes reply => do
    let t ← (rt.table.get : BaseIO (Table Port))
    if t.writable key then
      let r ← putData rt key bytes
      answer (some reply) r
    else
      -- A reset answers `reset`; our own close or the session end
      -- answers `closed`.
      let cause ← (port.cause : BaseIO (Option Streams.Error))
      answer (some reply) (.error (cause.getD .closed))
  | .close key reply => do
    let due ← (rt.table.updateGet (Table.closeLocal key) : BaseIO Bool)
    if due then
      let r ← put rt (encodeB (closeFlag key) key.id .empty)
      answer (some reply) r
    else answer (some reply) (.ok ())

/-- The writer task: every item in queue order, until the teardown
closes the queue and the queue is empty. -/
private def writer (rt : Runtime) : Async Unit := do
  repeat
    -- Park: a stream operation wakes it, and the teardown closes the
    -- queue.
    let some item ← rt.out.recv | break
    perform rt item

/-! ## The reader -/

/-- Apply one inbound message. `.error` is a protocol error that ends
the session. -/
private def dispatch (rt : Runtime) (f : Frame) : Async (Except Core.Error Unit) := do
  match classify f.flag f.id with
  | .open key =>
    let port ← (Port.new : BaseIO Port)
    match ← (rt.table.updateGet (Table.openRemote f.id port) : BaseIO OpenAnswer) with
    | .accepted =>
      -- Park: `accept` wakes it, and the session close closes the
      -- queue. A closed queue leaves the stream to the teardown.
      discard <| rt.accepts.send (streamOf rt key port)
      return .ok ()
    | .duplicate => return .error (.protocol s!"mplex: NewStream for the live stream {f.id}")
    | .full =>
      discard <| (rt.out.trySend (.raw (encodeB (resetFlag key) key.id .empty) none) : BaseIO Bool)
      return .ok ()
    | .ended => return .ok ()
  | .data key =>
    if f.payload.isEmpty then return .ok ()
    let t ← (rt.table.get : BaseIO (Table Port))
    if let some port := t.dataPort? key then
      -- Park: a read wakes it. A reset or the session close closes the
      -- inbox, and the send then fails at once.
      discard <| port.inbox.send f.payload
    return .ok ()
  | .close key =>
    if let some port ← (rt.table.updateGet (Table.closeRemote key) : BaseIO (Option Port)) then
      port.inbox.close
    return .ok ()
  | .reset key =>
    if let some port ← (rt.table.updateGet (Table.resetRemote key) : BaseIO (Option Port)) then
      port.abort .reset
    return .ok ()

/-- The reader loop. `buf` holds the bytes from `pos` on that no
message has taken yet. The loop reads the connection only when the
buffer holds no complete message, so the buffer holds at most one
partial message, under the cap, and one read. -/
private def readLoop (rt : Runtime) (leftover : ByteArray) : Async (Except Core.Error Unit) := do
  let mut buf := leftover
  let mut pos := 0
  repeat
    match decodeAtB? buf pos with
    | .ok (frame, next) =>
      pos := next
      if let .error e ← dispatch rt frame then return .error e
    | .error .malformed => return .error (.protocol "mplex: malformed message")
    | .error .truncated =>
      let chunk ← try rt.conn.read catch e => do
        rt.outcome.recordFault e
        pure none
      match chunk with
      | none => return .ok ()
      | some c =>
        buf := buf.extract pos buf.size ++ c
        pos := 0
  return .ok ()

/-- End every stream, and refuse new ones. A stream whose peer
direction was open reads `.error .closed` once. -/
private def endStreams (rt : Runtime) : BaseIO Unit := do
  let entries ← rt.table.updateGet Table.endAll
  for (_, e) in entries do
    if e.halves.remoteOpen then e.port.abort .closed else e.port.inbox.close

/-- The teardown of the reader: record the answer first, so a fault
the close causes records nothing (`Conc.Outcome`), then end every
stream and wait. -/
private def teardown (rt : Runtime) (result : Except Core.Error Unit) : IO Unit := do
  rt.outcome.finish result
  endStreams rt
  rt.accepts.close
  -- The streams still queued for `accept` have ended already.
  discard rt.accepts.drain
  rt.out.close
  rt.conn.close

/-! ## The session -/

/-- Start a session over `conn`. `leftover` holds the bytes the muxer
negotiation read past its last message; the reader decodes them
first. Both sides number their streams from zero, so the session takes
no role. -/
def start (conn : Streams.Connection) (leftover : ByteArray) : BaseIO MuxSession := do
  let rt : Runtime := {
    conn
    table := ← OnceRef.new Table.empty
    accepts := ← Chan.new acceptCap
    out := ← Chan.new outboundCap
    outcome := ← Outcome.new
    tasks := ← TaskSet.new }
  rt.tasks.spawn do
    let result ← readLoop rt leftover
    teardown rt result
  rt.tasks.spawn (writer rt)
  return {
    openStream := fun pid => ExceptT.mk do
      let port ← (Port.new : BaseIO Port)
      let some key ← (rt.table.updateGet (Table.openLocal port) : BaseIO (Option Key))
        | return .error (.closed "mplex: the session refused the stream")
      -- The stream name is a label only (the spec, "Opening a new
      -- stream"). The session writes the protocol id there.
      let label := (Bytes.ofString pid.toString).extract 0 Libp2p.Mux.mplexMessageCap
      match ← submit rt fun reply => .raw (encodeB .newStream key.id label) (some reply) with
      | .ok () => return .ok (streamOf rt key port)
      | .error _ =>
        rt.table.update (Table.forget key)
        return .error (.closed "mplex: the session ended")
    -- Park: the reader's offer wakes it, and the close closes the queue.
    accept := rt.accepts.recv
    close := do
      rt.outcome.markClosing
      endStreams rt
      rt.accepts.close
      rt.conn.close
    join := ExceptT.mk do
      rt.tasks.joinAll
      rt.outcome.answer }

end Libp2p.Mux.Mplex.Session
