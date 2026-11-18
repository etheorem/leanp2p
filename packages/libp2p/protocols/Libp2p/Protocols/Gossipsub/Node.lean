import Conc
import Streams
import Bytes
import Libp2p.Protocols.Constants
import Libp2p.Core
import Libp2p.Protocols.StreamError
import Libp2p.Protocols.Gossipsub.HostSeam
import Libp2p.Protocols.Gossipsub.Core
import Libp2p.Protocols.Gossipsub.Payload

/-!
# Gossipsub node: the loop over the router core

The core of this unit is the pure `Core.step`. This module holds the one
task that drives it, and the publish and subscribe surface at the seam
level (ARCHITECTURE, "Modules"; root ARCHITECTURE §3.3).

## The loop

One task owns the router state. A bounded channel carries application and
host events and the wakes of Conc.Alarm. The alarm has its own task. The
loop uses repeat and parks only on the channel receive. Ready events use
constant stack space. The loop asks the alarm for the next due time after
each input. A TestClock drives the alarm in tests.

The inbound reader uses repeat with a mutable header, body cursor and chunk
position. Each bounded body allocation follows its decoded length. Each
input byte enters the body once, so small reads use constant stack space
and linear copying.

## Ownership

The task set of the node owns the loop, alarm and writer tasks. Stop joins
them. The host owns the handler tasks of the inbound streams. Nothing cancels a task:
`stop` closes the event queue, and the close wakes the parked loop. The
router state and pending gossip are local to the loop. Shared registries,
subscriptions and the closing flag change through OnceRef.update or
updateGet (root ARCHITECTURE §4.1). Only the first stop caller joins.

## Recorded decisions

- **The stop field runs in Async.** Joining parks, and TaskSet.joinAll runs
  in Async for that reason. So the field keeps that type and leaves the
  blocking run to the application edge.
- **Actions never park.** Each send offers a frame to a peer queue with 32
  slots. One writer task owns that peer's stream. A full queue drops the
  frame, as go does for a full peer queue. Node.dropped reports these drops.
  Actions return the next pending list, and the loop assigns that answer.
- **The records of our own state come back after a drop.** Gossip and
  messages stay dropped, because the peer can ask again. A GRAFT or PRUNE
  record waits for the next frame to the peer, or for the heartbeat, if it
  still holds then. A subscription record is sent again after a random wait
  of up to one second, if it still holds then. Both follow go (`enqueue`).
- **Delayed gossip has a bound.** At most 256 sends wait in the pending list.
  Overflow drops the newest excess sends and adds to Node.dropped. Due sends
  leave before the tick shifts the message cache. The delay index increases
  across the run. Config.order hashes the heartbeat count with peer bytes.
- **Subscribe registers its callback before the post.** The loop can serve a
  delivery between the post and the registration, and that delivery would
  miss the callback. A refused post takes back its own registration by id.
  Concurrent callers remove their own entries through atomic updates.
- **The handler announces its opener.** It posts peerJoined before reading
  frames, so the first RPC reaches a known peer. Repeat joins are no-ops.
- **No signer.** The core validates with `strictNoSign` (`Core.validationOk`),
  which requires `from` and `seqno` to be absent. So `publish` signs nothing
  and never writes the peer id of the node.
- **A local publish delivers nothing locally.** `Core.publishLocal` emits no
  deliver action, because the application already holds its own message.
  The callback of the publisher stays silent.
- **The loop announces a subscription change.** `Core.join` sends the topics
  only when a peer joins. The core emits nothing for a subscribe after the
  join, so that peer would never learn the topic. The go implementation
  announces a change in its host registry, outside the router. The loop
  does the same with subOptRpc, before the core step.
- **The default gossip delay is zero.** The pinned go router enqueues IHAVEs
  in emitGossip (gossipsub.go, lines 2007 to 2076). Its flush sends them at
  once (lines 2078 to 2092). The random sleep in announceRetry belongs to a
  subscription retry (pubsub.go, lines 1234 to 1235). The loop owns the
  emission schedule, so a caller can spread heartbeat gossip across the
  interval. The default spreads nothing and matches go. Tests configure an
  explicit spread because issue #23 names the trickle regressions. The delay
  applies only to heartbeat IHAVEs. Publish, forward, graft and hello sends
  leave at once.
- **Each peer has one inbound stream.** A second inbound stream of a peer
  resets the first, and its handler waits for the first handler to end, as
  go-libp2p-pubsub v0.19.0 does (comm.go, lines 77 to 90). `handler` keeps
  the table.
- **Each peer has one writer task.** The pinned go pubsub version a01777894f4c
  uses one stream and a bounded queue per peer (comm.go, lines 181 to 233).
  Our writer
  writes frames in queue order. A failed write retires its outbound entry
  and closes its queue. Transport notifications own peerLeft. Stop resets
  installed streams to wake parked writes and joins
  the writer tasks. The host must end a newStream call when its session ends.
- **The inbound handler serves every frame of a stream.** The pubsub spec
  uses separate long-lived inbound and outbound streams (pubsub/README.md,
  lines 78 to 83). Go reads messages in a loop (comm.go, lines 75 to 120).
  Rust keeps one inbound substream (protocols/gossipsub/src/handler.rs,
  lines 78 to 82). Both peers write many RPCs on one stream. The handler
  preserves frame order and checks each length before appending body bytes.
  A bad prefix, an over-cap frame or EOF inside a frame is a protocol error.
  A zero-length frame is legal (Rpc.lean, line 867). Go skips it; this handler
  decodes it as an empty RPC that the core accepts.
- **The receipt observer runs before the core step.** The interop harness
  logs every received message, including duplicates (gossipsub-interop,
  test-specs/implementation.md, lines 71 to 78). Its go participant logs
  messages on RECV_RPC (go-libp2p/tracer.go, lines 75 to 88). Core.handlePubs
  deduplicates before delivery (Core.lean, lines 603 and 614). Config.onRpc
  exposes the sender and unframed body before that step. The observer can
  decode the body to log every message. The default hook decodes nothing.
  Frame errors fail the handler before they reach the observer.
- **A send failure retires its outbound entry.** The next send starts a fresh
  writer and stream. The core keeps the peer and accepts further RPCs on its
  live inbound stream. Retirement checks the writer id, so an old writer
  cannot remove a newer entry for the same peer.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Node


/-- A spread a caller may choose for heartbeat gossip. Each delay stays below
one second. The multiplier is prime, so the delays do not repeat with a short
period. Config.trickle defaults to zero. A caller who needs gossip inside
each heartbeat interval sets heartbeatInterval above the largest delay. -/
def spread (i : Nat) : Millis := (i * 7919 + 1) % 1000

/-- Replayable peer order for a heartbeat. The hash combines its counter
with each peer's identity bytes. The loop supplies only known peers. -/
def defaultOrder (tick : Nat) (peers : List Peer) : List Peer :=
  let key (peer : Peer) : UInt64 := mixHash (hash tick) (hash (Bytes.toNatList peer.toBytes))
  peers.mergeSort (fun a b => key a ≤ key b)

/-- The configuration of one node: the router parameters, the clock the
loop reads, and the spread of the heartbeat gossip. -/
structure Config where
  /-- The router parameters. -/
  params : Core.Params := Core.defaults
  /-- The clock of the loop's timer. -/
  clock : Conc.Clock := Conc.Clock.system
  /-- The delay of the run-wide `i`-th delayed gossip send, in milliseconds.
  The caller fixes it, so a test gets exact times. -/
  trickle : Nat → Millis := fun _ => 0
  /-- Replayable peer order for the numbered heartbeat. -/
  order : Nat → List Peer → List Peer := defaultOrder
  /-- Called for every inbound RPC with its sender and its bytes, before the
  core sees them. A harness reads it to log each received message, including
  a duplicate. It runs on the loop task, so it must not park. -/
  onRpc : Peer → List Nat → BaseIO Unit := fun _ _ => pure ()
  /-- Called for every outbound RPC before it enters the peer queue. -/
  onSend : Peer → Rpc.RPC → BaseIO Unit := fun _ _ => pure ()
  /-- The `ByteArray` payload path (`Gossipsub.Payload`): the message id of
  a payload on a topic, or `none` for a local fault such as a failed hash.
  When set, the node keeps every payload as a `ByteArray`, and the core
  sees only its id, so a block-sized message never becomes a `List Nat`.
  The node then sets `params.msgId` to read the handle. A delivery
  callback gets the message with its handle in `data`, and `Node.payload`
  reads the bytes. An inbound RPC with a payload that has no id is
  dropped, and a publish with no id answers `false`. -/
  payloadId : Option (String → ByteArray → Option MessageId) := none

/-- A running node. Every field is a seam over the loop task, which is the
only owner of the router state. -/
structure Node where
  /-- Publish the payload on the topic. `false` when the queue of the loop
  is full or the node stopped. -/
  publish : TopicId → ByteArray → BaseIO Bool
  /-- Register a delivery callback. The callback runs on the loop task, so
  it must not park. `false` under the same conditions as `publish`, and the
  callback then stays unregistered. -/
  subscribe : TopicId → (Message → BaseIO Unit) → BaseIO Bool
  /-- `subscribe`, which parks while the queue of the loop is full. A
  consensus node subscribes to about 200 topics at once, more than the
  queue holds, and `subscribe` refuses the ones past a full queue. `false`
  only when the node stopped, and the callback then stays unregistered.
  The loop task must not call it: a callback that parks on the loop's own
  queue would wait on itself. -/
  subscribeWait : TopicId → (Message → BaseIO Unit) → Conc.Async Bool
  /-- Drop every callback of the topic, and leave the topic. `false` under the
  same conditions as `publish`. -/
  unsubscribe : TopicId → BaseIO Bool
  /-- Tell the loop that a peer joined. The connection notifiee of the host
  is the caller at integration. -/
  peerJoined : Peer → Core.PubsubProto → BaseIO Bool
  /-- Tell the loop that a peer left. -/
  peerLeft : Peer → BaseIO Bool
  /-- Close the event queue and join the loop task. The loop serves the
  queued events first, and drops the gossip that waits for its time. This
  field runs in `Async` because a join parks, and a parked `BaseIO` action would
  hold a thread. A second call does nothing. -/
  stop : Conc.Async Unit
  /-- Frames dropped by a full or closed peer queue, or by the 256-send
  pending-gossip bound. -/
  dropped : BaseIO Nat
  /-- The payload of a message id on the `ByteArray` path
  (`Config.payloadId`). `none` off that path, or once the payload expired
  with the message cache. -/
  payload : MessageId → BaseIO (Option ByteArray)

/-! ## One outbound RPC -/

/-- True when the control message of the RPC holds an IHAVE. The loop
delays these sends. `Core.rpcHasIhave` is a `Prop`, and the loop needs a `Bool`. -/
def hasIhave (r : Rpc.RPC) : Bool :=
  match r.control with
  | some c => !c.ihave.isEmpty
  | none => false

/-- One subscription record: `true` subscribes, and `false` unsubscribes.
`Core.helloRpc` holds only positive records, so the loop builds this record
beside the code that sends it. -/
def subOptRpc (t : TopicId) (on : Bool) : Rpc.RPC :=
  { subscriptions := [{ subscribe := on, topicid := t.name }], publish := [], control := none }

/-- The one input queue carries core events, alarm wakes, and the retries
of dropped subscription records (`scheduleRetry`). -/
inductive Input where
  | event (e : Core.Event)
  | wake (now : Millis)
  | retry (peer : Peer) (topic : TopicId) (sub : Bool)

/-- One peer's bounded writer queue and its currently open stream. -/
structure Outbound where
  /-- The writer generation used for exact retirement. -/
  id : Nat
  /-- At most 32 encoded frames wait for this peer. -/
  queue : Conc.Chan ByteArray
  /-- Stop resets this stream to wake a parked write. -/
  stream : Conc.OnceRef (Option Streams.Stream)

/-- Close a queue and reset its stream to wake its writer. -/
private def endOutbound (ob : Outbound) : Conc.Async Unit := do
  (ob.queue.close : BaseIO Unit)
  if let some stream ← (ob.stream.get : BaseIO (Option Streams.Stream)) then
    stream.reset

/-- One writer owns the peer stream. It writes queued frames in order and
closes the stream at the end. A failed open or write retires only this writer
entry and closes its queue. The core peer stays connected. Stop resets an
installed stream; a late open checks closing too. -/
private def writer (host : HostSeam) (closing : Conc.OnceRef Bool)
    (outbound : Conc.OnceRef (List (Peer × Outbound))) (peer : Peer) (ob : Outbound) : Conc.Async Unit := do
  let fail : Conc.Async Unit := do
    (ob.queue.close : BaseIO Unit)
    (outbound.update (fun table => table.filter (fun e => e.2.id != ob.id)) : BaseIO Unit)
    if let some stream ← (ob.stream.get : BaseIO (Option Streams.Stream)) then stream.reset
  try
    match ← host.newStream peer [Constants.meshsubId] with
    | .error _ => fail
    | .ok (_, stream) =>
      (ob.stream.set (some stream) : BaseIO Unit)
      if ← (closing.get : BaseIO Bool) then stream.reset
      repeat
        match ← ob.queue.recv with
        | none => break
        | some frame =>
          if let .error _ ← stream.write frame then
            fail
            break
      stream.close
  catch _ => fail

/-! ## The inbound handler -/

/-- Read consecutive frames with a bounded header and one body allocation.
The header is at most Varint.maxBytes bytes. Its decoded length is capped
before emptyWithCapacity allocates the body. This is the pinned Lean name
for the capacity constructor. Each copySlice writes only the next slice at
cursor, without retaining an earlier body value. EOF between frames is clean.
The repeat loop uses constant stack space for any number of chunks or frames. -/
private def readFrames (events : Conc.Chan Input)
    (split : ByteArray → BaseIO (Option ByteArray)) (peer : Peer)
    (stream : Streams.Stream) : Conc.Async (Except Libp2p.Core.Error Unit) := do
  let mut header := ByteArray.emptyWithCapacity Varint.maxBytes
  let mut body := ByteArray.empty
  let mut expected : Option Nat := none
  let mut cursor := 0
  let mut chunk := ByteArray.empty
  let mut pos := 0
  repeat
    if let some size := expected then
      if cursor = size then
        -- On the payload path the core gets the RPC with handles. An RPC
        -- that the split refuses is dropped.
        if let some small ← (split body : BaseIO (Option ByteArray)) then
          -- Park: the loop frees a slot, or stop closes the event queue.
          if let .error _ ← events.send (.event (.rpc peer (Bytes.toNatList small))) then
            return .ok ()
        body := ByteArray.empty
        expected := none
        cursor := 0
    if pos = chunk.size then
      -- Park: the peer writes, half-closes, or resets.
      match ← stream.read with
      | .error e => return .error (mapStreamError e)
      | .ok none =>
        return if header.isEmpty && expected.isNone then .ok ()
          else .error (.protocol "the stream ended inside an RPC frame")
      | .ok (some bytes) =>
        chunk := bytes
        pos := 0
    else
      match expected with
      | some size =>
        let count := Nat.min (size - cursor) (chunk.size - pos)
        body := chunk.copySlice pos body cursor count
        cursor := cursor + count
        pos := pos + count
      | none =>
        if Varint.maxBytes ≤ header.size then
          return .error (.protocol "the RPC header is malformed")
        header := header.push (chunk.get! pos)
        pos := pos + 1
        match Streams.Framing.decodeLength? .uvarint (Bytes.toNatList header) with
        | .error .truncated => pure ()
        | .error .malformed => return .error (.protocol "the RPC header is malformed")
        | .ok (size, _) =>
          if Constants.rpcCap < size then
            return .error (.protocol "the RPC exceeds the cap")
          -- The allocation runs only after the length passes the cap.
          body := ByteArray.emptyWithCapacity size
          expected := some size
          cursor := 0
          header := ByteArray.emptyWithCapacity Varint.maxBytes
  return .ok ()

/-- The inbound stream that the handler of a peer reads. `done` closes when
that handler ends. -/
structure Inbound where
  id : Nat
  stream : Streams.Stream
  done : Conc.Chan Unit

/-- The one inbound stream of each peer. -/
structure InboundTable where
  next : Nat
  entries : List (Peer × Inbound)

/-- Make `stream` the inbound stream of `peer`. The answer holds its entry id
and the entry it replaces. -/
private def installInbound (table : InboundTable) (peer : Peer) (stream : Streams.Stream)
    (done : Conc.Chan Unit) : (Nat × Option Inbound) × InboundTable :=
  let prev := (table.entries.find? (·.1 == peer)).map (·.2)
  ((table.next, prev),
    { next := table.next + 1
      entries := (peer, ⟨table.next, stream, done⟩) :: table.entries.filter (·.1 != peer) })

/-- Drop the entry `id` of `peer`. A newer stream of the peer owns the entry
after a replacement, and the drop leaves that one. -/
private def removeInbound (table : InboundTable) (peer : Peer) (id : Nat) : InboundTable :=
  { table with entries := table.entries.filter fun e => !(e.1 == peer && e.2.id == id) }

/-- Serve every RPC of a peer's stream in arrival order. Frame errors reset
both directions. A clean EOF closes our write direction. The host owns and
joins this handler task.

A peer has one inbound stream, as in go-libp2p-pubsub v0.19.0 (`comm.go`,
lines 77 to 90). A new stream replaces the entry of its peer in `inbound`,
resets the old stream, and waits for the old handler to end before it reads,
so the RPCs of the two streams do not mix. The reset wakes the parked read of
the old handler, and that handler ends with `.ok`. On exit a handler drops its
entry only when it still owns it (lines 60 to 65).

`split` turns each frame into the RPC the core gets: the frame as it is
by default, or the frame with handles on the payload path. -/
def handler (events : Conc.Chan Input) (inbound : Conc.OnceRef InboundTable)
    (split : ByteArray → BaseIO (Option ByteArray) := fun b => pure (some b)) :
    Libp2p.Core.StreamHandler where
  id := Constants.meshsubId
  handle ctx stream := ExceptT.mk do
    let peer := ctx.remotePeer
    let done : Conc.Chan Unit ← (Conc.Chan.new 1 : BaseIO (Conc.Chan Unit))
    let (id, prev) ← (inbound.updateGet (installInbound · peer stream done) :
      BaseIO (Nat × Option Inbound))
    try
      if let some old := prev then
        old.stream.reset
        -- Park: the old handler closes `done` as it ends.
        discard <| old.done.recv
      -- The opener joins before its first RPC. Repeat joins are loop no-ops.
      if let .error _ ← events.send (.event (.peerJoined peer .meshsub)) then
        stream.close
        return .ok ()
      let answer ← readFrames events split peer stream
      -- A replaced stream ends by the reset of its successor, which is no
      -- fault of the peer.
      let replaced ← (inbound.get : BaseIO InboundTable) <&> fun t =>
        !(t.entries.any fun e => e.1 == peer && e.2.id == id)
      match answer with
      | .ok () => stream.close; return .ok ()
      | .error _ =>
        stream.reset
        return if replaced then .ok () else answer
    finally
      (inbound.update (removeInbound · peer id) : BaseIO Unit)
      (done.close : BaseIO Unit)

/-! ## The subscription table -/

/-- One delivery callback. -/
private structure Subscription where
  /-- The unique registration id used by a refused post. -/
  id : Nat
  /-- The topic. -/
  topic : TopicId
  /-- The callback. -/
  callback : Message → BaseIO Unit

/-- The shared table of the callbacks, in registration order. -/
private structure Subscriptions where
  /-- The next unused registration id. -/
  next : Nat
  /-- The callbacks. -/
  entries : List Subscription

/-- Call every callback of the topic of `m`, in registration order. -/
private def deliver (subs : Conc.OnceRef Subscriptions) (m : Message) : BaseIO Unit := do
  for sub in (← subs.get).entries do
    if sub.topic = m.topic then
      sub.callback m

/-! ## The loop -/

/-- What the loop reads and never changes. -/
private structure Env where
  /-- The host seam. -/
  host : HostSeam
  /-- The configuration. -/
  config : Config
  /-- The subscription table. -/
  subs : Conc.OnceRef Subscriptions
  /-- The event queue. -/
  events : Conc.Chan Input
  /-- The owned alarm task posts wakes on events. -/
  alarm : Conc.Alarm
  /-- The owner of the loop, alarm and writers. -/
  tasks : Conc.TaskSet
  /-- The peer writer registry. The loop inserts and writers retire by id. -/
  outbound : Conc.OnceRef (List (Peer × Outbound))
  /-- The next writer generation, allocated atomically. -/
  nextOutbound : Conc.OnceRef Nat
  /-- The first stop caller sets this flag. -/
  closing : Conc.OnceRef Bool
  /-- Frames refused by a full or closed outbound queue. -/
  drops : Conc.OnceRef Nat
  /-- The payloads of the `ByteArray` path, by id, with the time each was
  stored. -/
  payloads : Conc.OnceRef (Std.HashMap MessageId (ByteArray × Millis))
  /-- The GRAFT and PRUNE records of a dropped frame, one entry per peer,
  for the next frame to that peer (`enqueue`). -/
  control : Conc.OnceRef (List (Peer × Rpc.ControlMessage))
  /-- `stop` closes it, which wakes every retry timer (`scheduleRetry`). -/
  halt : Conc.Chan Unit

/-- The frame of one RPC under the cap. On the payload path the published
messages carry handles, and the frame takes the stored payloads back
(`Payload.joinOutbound`). `none` when the RPC is over the cap. -/
private def frameOf (env : Env) (rpc : Rpc.RPC) : BaseIO (Option ByteArray) := do
  if env.config.payloadId.isSome && !rpc.publish.isEmpty then
    let store ← env.payloads.get
    let body := Payload.joinOutbound rpc (fun h => (store.get? h).map (·.1))
    return if body.size ≤ Constants.rpcCap then
      some (Bytes.ofNatList (Streams.Framing.encodeLength .uvarint body.size) ++ body)
      else none
  return (Rpc.encodeFrame? rpc).map Bytes.ofNatList

/-- The GRAFT and PRUNE records of a kept control message that still hold
for `peer` in `router`: a GRAFT while the peer is in the topic's mesh, and
a PRUNE while it is not. go-libp2p-pubsub v0.19.0 drops a stale record the
same way before it sends a kept one (`gossipsub.go`, lines 2152 to 2198). -/
private def freshControl (router : Core.State) (peer : Peer) (c : Rpc.ControlMessage) :
    Rpc.ControlMessage :=
  { ihave := [], iwant := []
    graft := c.graft.filter fun g => (Core.meshOf router ⟨g.topicId⟩).contains peer
    prune := c.prune.filter fun q => !(Core.meshOf router ⟨q.topicId⟩).contains peer }

/-- Add the GRAFT and PRUNE records of `extra` to `rpc`, one record per
topic and kind, so a control message that is kept again and again does not
grow. -/
private def withControl (rpc : Rpc.RPC) (extra : Rpc.ControlMessage) : Rpc.RPC :=
  if extra.graft.isEmpty && extra.prune.isEmpty then rpc
  else
    let c := rpc.control.getD { ihave := [], iwant := [], graft := [], prune := [] }
    let graft := extra.graft.foldl (fun gs g =>
      if gs.any (·.topicId == g.topicId) then gs else gs ++ [g]) c.graft
    let prune := extra.prune.foldl (fun ps q =>
      if ps.any (·.topicId == q.topicId) then ps else ps ++ [q]) c.prune
    { rpc with control := some { c with graft, prune } }

/-- Retry a dropped subscription record later. go-libp2p-pubsub v0.19.0
waits 1 to 1000 ms, and then sends the record again only when it still
holds (`announceRetry`, `pubsub.go`, lines 1373 to 1391). The timer task
posts `Input.retry`, and the loop makes the check. `stop` closes `halt`,
which wakes the timer, and the task ends. The node's task set owns it. -/
private def scheduleRetry (env : Env) (peer : Peer) (topic : TopicId) (sub : Bool) :
    BaseIO Unit := do
  let delay ← IO.rand 1 1000
  env.tasks.spawn do
    let timer ← (env.config.clock.after delay : BaseIO (Conc.Park Unit))
    -- Park: the timer fires, or `stop` closes `halt`.
    let fired ← Conc.select #[timer.map (fun _ => true), Conc.Park.recv env.halt (fun _ => false)]
    -- Park: the loop takes the input, or `stop` closes the queue.
    if fired then discard <| env.events.send (.retry peer topic sub)

/-- Encode and offer one RPC to a peer's queue. This operation never parks.
Each peer has one writer and one stream.

A full queue drops the frame, as go drops it for a full peer queue. The
frame of gossip or a message stays dropped: the peer can ask again. The
records of our own state come back. go-libp2p-pubsub v0.19.0 does this in
two ways, and the node follows both:

* A GRAFT or PRUNE record is kept for the peer (`pushControl`,
  `gossipsub.go`, lines 2142 to 2150). The next frame to the peer takes the
  records that still hold (`piggybackControl`), and the heartbeat sends the
  rest (`flush`, lines 2110 to 2124). The node keeps one control message per
  peer, so a peer's own requests cannot grow the table.
* A subscription record is sent again later, when it still holds
  (`scheduleRetry`). Without this, a node that subscribes to 200 topics at
  once loses most of its records to a peer whose queue is full, and the
  peer never learns the topics. -/
private def enqueue (env : Env) (router : Core.State) (peer : Peer) (rpc0 : Rpc.RPC) :
    BaseIO Unit := do
  if ← env.closing.get then return ()
  -- The kept records of an earlier drop go first, in this frame.
  let kept ← env.control.updateGet fun table =>
    ((table.find? (·.1 == peer)).map (·.2), table.filter (·.1 != peer))
  let rpc := match kept with
    | some c => withControl rpc0 (freshControl router peer c)
    | none => rpc0
  (env.config.onSend peer rpc : BaseIO Unit)
  let some frame ← frameOf env rpc | return ()
  let table ← env.outbound.get
  let ob ← match table.find? (fun e => e.1 == peer) with
    | some (_, ob) => pure ob
    | none => do
      let id ← env.nextOutbound.updateGet (fun n => (n, n + 1))
      let ob : Outbound := { id, queue := ← Conc.Chan.new 32, stream := ← Conc.OnceRef.new none }
      env.outbound.update (fun table => (peer, ob) :: table)
      env.tasks.spawn (writer env.host env.closing env.outbound peer ob)
      pure ob
  if ← env.closing.get then
    ob.queue.close
    return ()
  if !(← ob.queue.trySend frame) then
    env.drops.update (· + 1)
    -- Keep the GRAFT and PRUNE records for the next frame to the peer.
    if let some c := rpc.control then
      if !c.graft.isEmpty || !c.prune.isEmpty then
        env.control.update fun table =>
          (peer, { c with ihave := [], iwant := [] }) :: table.filter (·.1 != peer)
    -- Send each subscription record again later.
    for o in rpc.subscriptions do
      scheduleRetry env peer ⟨o.topicid⟩ o.subscribe

/-- Retire a peer writer after its disconnect event. The kept records for
the peer go too. -/
private def removePeer (env : Env) (peer : Peer) : BaseIO Unit := do
  env.control.update (·.filter (·.1 != peer))
  let removed ← env.outbound.updateGet fun table =>
    (table.filter (fun e => e.1 == peer), table.filter (fun e => e.1 != peer))
  for (_, ob) in removed do
    ob.queue.close
    env.tasks.spawn (endOutbound ob)

/-- One gossip send that waits for its due time. -/
private structure Pending where
  /-- The due time. -/
  due : Millis
  /-- The receiver. -/
  peer : Peer
  /-- The RPC. -/
  rpc : Rpc.RPC

/-- The local state of the loop. -/
private structure LoopState where
  /-- The router state. -/
  router : Core.State
  /-- The gossip sends that wait for their due time. -/
  pending : List Pending
  /-- The time of the next heartbeat. -/
  nextTick : Millis
  /-- The heartbeat count used for the peer order. -/
  ticks : Nat
  /-- The next run-wide delayed gossip index. -/
  gossipIndex : Nat

/-- Run the actions of one core step, in order, and answer the delayed
sends. `gossipAt` is the time of the tick when a tick made the actions. The
run-wide i-th IHAVE waits for trickle i milliseconds. Every other action
runs now. -/
private def perform (env : Env) (router : Core.State) (gossipAt : Option Millis) (index : Nat)
    (actions : List Core.Action) : BaseIO (List Pending × Nat) := do
  let mut delayed : Array Pending := #[]
  let mut gossipIndex := index
  for action in actions do
    match action with
    | .deliver m => (deliver env.subs m : BaseIO Unit)
    | .sendRpc to rpc =>
      match gossipAt with
      | some now =>
        if hasIhave rpc then
          let delay := env.config.trickle gossipIndex
          gossipIndex := gossipIndex + 1
          if delay = 0 then
            enqueue env router to rpc
          else
            delayed := delayed.push { due := now + delay, peer := to, rpc := rpc }
        else
          enqueue env router to rpc
      | none => enqueue env router to rpc
  return (delayed.toList, gossipIndex)

/-- Tell peers about a subscription change, or tell a new peer about all
current subscriptions. Each offer uses the bounded per-peer queue. -/
private def announce (env : Env) (st : LoopState) (event : Core.Event) :
    BaseIO LoopState := do
  match event with
  | .subscribe t =>
    let rpc := subOptRpc t true
    for (peer, _) in st.router.peers do
      enqueue env st.router peer rpc
  | .unsubscribe t =>
    let rpc := subOptRpc t false
    for (peer, _) in st.router.peers do
      enqueue env st.router peer rpc
  | .peerJoined peer _ =>
    if !st.router.topics.isEmpty then
      enqueue env st.router peer (Core.helloRpc st.router.topics)
  | _ => pure ()
  return st

/-- Drop the core hello when the node already sent per-topic join records. -/
private def withoutPeerHello (peer : Peer) (topics : List TopicId) :
    List Core.Action → List Core.Action
  | [] => []
  | action :: rest =>
    match action with
    | .sendRpc target rpc =>
      if !topics.isEmpty && target == peer && rpc == Core.helloRpc topics then
        withoutPeerHello peer topics rest
      else action :: withoutPeerHello peer topics rest
    | _ => action :: withoutPeerHello peer topics rest

/-- One core step, then its actions. Only an RPC that does not decode makes
the core answer `.error`. That answer keeps the state, and the loop runs on. -/
private def stepAndAct (env : Env) (st : LoopState) (event : Core.Event) : BaseIO LoopState := do
  if let .peerJoined peer _ := event then
    if (Core.peerOf st.router peer).isSome then return st
  let st ← announce env st event
  if let .rpc peer bytes := event then
    (env.config.onRpc peer bytes : BaseIO Unit)
  let st ← match event with
    | .peerLeft peer => do
      removePeer env peer
      pure { st with pending := st.pending.filter (fun p => p.peer != peer) }
    | _ => pure st
  match Core.step env.config.params st.router event with
  | .error (.decode _) => return st
  | .ok (router, actions) =>
    let actions := match event with
      | .peerJoined peer _ => withoutPeerHello peer st.router.topics actions
      | _ => actions
    let gossipAt := match event with
      | .tick now _ => some now
      | _ => none
    let (delayed, gossipIndex) ← perform env router gossipAt st.gossipIndex actions
    let all := st.pending ++ delayed
    let overflow := all.length - 256
    if 0 < overflow then env.drops.update (· + overflow)
    return { st with router, gossipIndex, pending := all.take 256 }

/-- The next wake is the first due send or the next heartbeat. -/
private def dueOf (st : LoopState) : Millis :=
  st.pending.foldl (fun due p => Nat.min due p.due) st.nextTick

/-- Send due gossip before the heartbeat shifts the message cache. -/
private def onWake (env : Env) (st : LoopState) (now : Millis) : BaseIO LoopState := do
  let (due, later) := st.pending.partition (fun p => decide (p.due ≤ now))
  for p in due.mergeSort (fun a b => decide (a.due ≤ b.due)) do
    enqueue env st.router p.peer p.rpc
  let st := { st with pending := later }
  if st.nextTick ≤ now then
    -- A stored payload lives one heartbeat past the message cache's window,
    -- so an IWANT answer still finds it.
    if env.config.payloadId.isSome then
      let ttl := (env.config.params.window.historyLength + 1) * env.config.params.heartbeatInterval
      env.payloads.update fun m => m.filter fun _ (_, t) => now < t + ttl
    let order := env.config.order st.ticks (st.router.peers.map (·.1))
    let st ← stepAndAct env st (.tick now order)
    -- The kept control records that no frame took go out on their own, as
    -- go's heartbeat flushes them (`enqueue`). A record that no longer
    -- holds goes, and a peer with none left gets no frame.
    let kept ← (env.control.updateGet (fun table => (table, [])) :
      BaseIO (List (Peer × Rpc.ControlMessage)))
    for (peer, c) in kept do
      let fresh := freshControl st.router peer c
      if !fresh.graft.isEmpty || !fresh.prune.isEmpty then
        enqueue env st.router peer { subscriptions := [], publish := [], control := some fresh }
    return { st with nextTick := now + env.config.params.heartbeatInterval, ticks := st.ticks + 1 }
  return st

/-- Run the core through one receive park. Each action returns its state.
The closed channel serves queued inputs before it returns none. The tail
closes the alarm and every cached outbound stream. -/
private def loop (env : Env) (st0 : LoopState) : Conc.Async Unit := do
  let mut st := st0
  (env.alarm.set (dueOf st) : BaseIO Unit)
  repeat
    match ← env.events.recv with
    | none => break
    | some (.wake now) => st ← (onWake env st now : BaseIO LoopState)
    | some (.event e) =>
      st ← (stepAndAct env st e : BaseIO LoopState)
    | some (.retry peer topic sub) =>
      -- Send the record again only while it still holds: the peer is
      -- known, and our subscription matches it (`scheduleRetry`).
      if (Core.peerOf st.router peer).isSome && st.router.topics.contains topic == sub then
        (enqueue env st.router peer (subOptRpc topic sub) : BaseIO Unit)
    (env.alarm.set (dueOf st) : BaseIO Unit)
  (env.alarm.close : BaseIO Unit)
  for (_, ob) in ← (env.outbound.get : BaseIO (List (Peer × Outbound))) do
    (ob.queue.close : BaseIO Unit)

/-- The router state of a node with no peers at time `now`. -/
private def initialState (p : Core.Params) (now : Millis) : Core.State :=
  { peers := []
    mesh := []
    fanout := []
    mcache := Cache.MessageIndex.empty p.window
    seen := Cache.SeenIndex.empty p.seen
    backoff := []
    iwant := []
    topics := []
    now := now
    lastHeartbeat := now
    lastDecay := now }

/-- The published message of a payload. The four signed fields stay absent,
as `strictNoSign` requires. -/
private def messageOf (topic : TopicId) (payload : ByteArray) : Message :=
  { «from» := none
    data := some (Bytes.toNatList payload)
    seqno := none
    topic := topic
    signature := none
    key := none }

/-- Build the state, register the handler, and start the loop. The event
queue holds 64 events. A full queue parks an inbound handler, which carries
the back-pressure to the peer, and it refuses a `BaseIO` post of the
application. `subscribeWait` is the one application post that parks. -/
def start (host : HostSeam) (config : Config := {}) : BaseIO Node := do
  -- On the payload path a message's `data` is its handle, the id bytes, so
  -- the core's id function reads it back.
  let config := if config.payloadId.isSome then
      { config with params := { config.params with msgId := fun m => ⟨m.data.getD []⟩ } }
    else config
  let now ← config.clock.nowMs
  let subs : Conc.OnceRef Subscriptions ← Conc.OnceRef.new { next := 0, entries := [] }
  let events : Conc.Chan Input ← Conc.Chan.new 64
  let inbound : Conc.OnceRef InboundTable ← Conc.OnceRef.new { next := 0, entries := [] }
  let payloads ← Conc.OnceRef.new ({} : Std.HashMap MessageId (ByteArray × Millis))
  -- The inbound split of the payload path (`Payload.splitInbound`). A
  -- malformed RPC goes to the core as it came, and the core's decoder
  -- reports it. An RPC with a payload that has no id is dropped.
  let split : ByteArray → BaseIO (Option ByteArray) := fun body => do
    match config.payloadId with
    | none => return some body
    | some idOf =>
      match Payload.splitInbound body idOf with
      | .error .malformed => return some body
      | .error .noId => return none
      | .ok (small, ps) =>
        let t ← config.clock.nowMs
        payloads.update fun m =>
          ps.foldl (fun m (id, d) => if m.contains id then m else m.insert id (d, t)) m
        return some small
  host.setHandler (handler events inbound split)
  let tasks ← Conc.TaskSet.new
  let alarm ← Conc.Alarm.new
  let outbound ← Conc.OnceRef.new ([] : List (Peer × Outbound))
  let nextOutbound ← Conc.OnceRef.new 0
  let closing ← Conc.OnceRef.new false
  let drops ← Conc.OnceRef.new 0
  tasks.spawn <| alarm.run config.clock (fun now => events.send (.wake now))
  let control ← Conc.OnceRef.new ([] : List (Peer × Rpc.ControlMessage))
  let halt : Conc.Chan Unit ← Conc.Chan.new 1
  tasks.spawn <| loop
    { host, config, subs, events, alarm, tasks, outbound, nextOutbound, closing, drops, payloads,
      control, halt }
    { router := initialState config.params now
      pending := []
      nextTick := now + config.params.heartbeatInterval
      ticks := 0
      gossipIndex := 0 }
  let post : Core.Event → BaseIO Bool := fun e => do
    if ← closing.get then return false
    events.trySend (.event e)
  -- The post that parks: it waits for room, and the stop closes the queue.
  let postWait : Core.Event → Conc.Async Bool := fun e => do
    if ← (closing.get : BaseIO Bool) then return false
    match ← events.send (.event e) with
    | .ok () => return true
    | .error _ => return false
  -- One callback entry, and its removal when the post fails.
  let register : TopicId → (Message → BaseIO Unit) → BaseIO Nat := fun topic callback =>
    subs.updateGet fun s =>
      (s.next,
        { next := s.next + 1
          entries := s.entries ++ [{ id := s.next, topic, callback }] })
  let unregister : Nat → BaseIO Unit := fun id =>
    subs.update fun s => { s with entries := s.entries.filter (fun entry => entry.id != id) }
  return {
    publish := fun topic payload =>
      match config.payloadId with
      | some idOf =>
        -- The payload path: store the bytes, and publish the handle. A
        -- payload with no id is a local fault, and the publish fails.
        match idOf topic.name payload with
        | none => pure false
        | some id => do
          let t ← config.clock.nowMs
          payloads.update (·.insert id (payload, t))
          post (.publish { messageOf topic .empty with data := some id.bytes })
      | none => post (.publish (messageOf topic payload))
    subscribe := fun topic callback => do
      if ← closing.get then return false
      let id ← register topic callback
      let sent ← post (.subscribe topic)
      if !sent then unregister id
      return sent
    subscribeWait := fun topic callback => do
      if ← (closing.get : BaseIO Bool) then return false
      let id ← (register topic callback : BaseIO Nat)
      -- Park: the loop takes a queued input, or the stop closes the queue.
      let sent ← postWait (.subscribe topic)
      if !sent then (unregister id : BaseIO Unit)
      return sent
    unsubscribe := fun topic => do
      if ← closing.get then return false
      subs.update fun s => { s with entries := s.entries.filter (fun e => e.topic != topic) }
      post (.unsubscribe topic)
    peerJoined := fun peer proto => post (.peerJoined peer proto)
    peerLeft := fun peer => post (.peerLeft peer)
    dropped := drops.get
    payload := fun id => do return ((← payloads.get).get? id).map (·.1)
    stop := do
      let first ← (closing.updateGet (fun was => (!was, true)) : BaseIO Bool)
      if first then
        (events.close : BaseIO Unit)
        -- Wake every retry timer, so its task ends (`scheduleRetry`).
        (halt.close : BaseIO Unit)
        for (_, ob) in ← (outbound.get : BaseIO (List (Peer × Outbound))) do
          endOutbound ob
        tasks.joinAll }

end Libp2p.Protocols.Gossipsub.Node
