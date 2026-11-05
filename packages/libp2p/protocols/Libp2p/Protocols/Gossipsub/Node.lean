import Conc
import Streams
import Bytes
import Libp2p.Protocols.Constants
import Libp2p.Protocols.Mock.Core
import Libp2p.Protocols.Mock.Host
import Libp2p.Protocols.Gossipsub.Core

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

The inbound readFrames is partial because a peer controls the number of
frames and chunks before EOF (root CLAUDE.md, "partial def").

## Ownership

The task set of the node owns the loop, alarm and writer tasks. Stop joins them. The host
owns the handler tasks of the inbound streams. Nothing cancels a task:
`stop` closes the event queue, and the close wakes the parked loop. The
router state and pending gossip are local to the loop. Shared registries,
subscriptions and the closing flag change through OnceRef.update or
updateGet (root ARCHITECTURE §4.1). Only the first stop caller joins.

## Recorded decisions

- **The stop field runs in Async.** The brief gives it a BaseIO type.
  TaskSet.joinAll runs in Async, because joining can park. This field keeps
  that type and leaves the blocking run to the application edge.
- **Actions never park.** Each send offers a frame to a peer queue with 32
  slots. One writer task owns that peer's stream. A full queue drops the
  frame, as go does for a full peer queue. Node.dropped reports these drops.
  Actions return the next pending list, and the loop assigns that answer.
- **The spread index counts sends within each heartbeat.** Config describes
  this index, while the brief's loop sketch increments it once per tick.
  Each delayed send gets its own index, and the next heartbeat starts at 0.
- **A refused subscribe removes its callback.** The cell changes before the
  post, so a refused post removes that registration by its unique id.
- **The queue carries Core.Event directly.** The loop owns all delayed sends,
  so no external sender needs the brief's unused send message constructor.
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
  does the same with `subOptRpc`, after the core step.
- **The default gossip delay is zero.** The pinned go router enqueues IHAVEs
  in emitGossip (gossipsub.go, lines 2007 to 2076). Its flush sends them at
  once (lines 2078 to 2092). The random sleep in announceRetry belongs to a
  subscription retry (pubsub.go, lines 1234 to 1235). The loop owns the
  emission schedule, so a caller can spread heartbeat gossip across the
  interval. The default spreads nothing and matches go. Tests configure an
  explicit spread because issue #23 names the trickle regressions. The delay
  applies only to heartbeat IHAVEs. Publish, forward, graft and hello sends
  leave at once.
- **Each peer has one writer task.** The pinned go pubsub version a01777894f4c
  resets duplicate inbound streams (comm.go, lines 55 to 65). Its sender uses
  one stream and a bounded queue per peer (lines 181 to 233). Our writer
  writes frames in queue order. A failed write closes the queue and posts
  peerLeft. Stop resets installed streams to wake parked writes and joins
  the writer tasks. The host must end a newStream call when its session ends.
- **The inbound handler serves consecutive frames.** Go keeps one reader
  loop per stream (comm.go, lines 75 to 120). Go and rust write many RPCs on
  one stream. A one-frame rule would break interop on the second RPC. The
  handler bounds each frame before appending bytes and preserves frame order.
- **The receipt observer runs before the core step.** The interop harness
  logs every received message, including duplicates (gossipsub-interop,
  test-specs/implementation.md, lines 71 to 78). Its go participant logs
  messages on RECV_RPC (go-libp2p/tracer.go, lines 75 to 88). Core.handlePubs
  deduplicates before delivery (Core.lean, lines 603 and 614). Config.onRpc
  exposes the sender and unframed body before that step. The observer can
  decode the body to log every message. The default hook decodes nothing.
  Frame errors fail the handler before they reach the observer.
- **The host posts `peerJoined` before it serves a stream of that peer.** The
  core ignores an RPC from an unknown peer (`Core.rpcStep`), so an earlier
  stream loses its RPC.
- **A send failure has no sink.** The send retires the stream, and the mock host has
  no failure log. The host reports stream failures at integration.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Node

open Mock.Host (HostSeam)

/-- A spread a caller may choose for heartbeat gossip. Each delay stays below
one second. The multiplier is prime, so the delays do not repeat with a short
period. Config.trickle defaults to zero. -/
def spread (i : Nat) : Millis := (i * 7919 + 1) % 1000

/-- The configuration of one node: the router parameters, the clock the
loop reads, and the spread of the heartbeat gossip. -/
structure Config where
  /-- The router parameters. -/
  params : Core.Params := Core.defaults
  /-- The clock of the loop's timer. -/
  clock : Conc.Clock := Conc.Clock.system
  /-- The delay of the `i`-th gossip send of one heartbeat, in milliseconds.
  The caller fixes it, so a test gets exact times. -/
  trickle : Nat → Millis := fun _ => 0
  /-- Called for every inbound RPC with its sender and its bytes, before the
  core sees them. A harness reads it to log each received message, including
  a duplicate. It runs on the loop task, so it must not park. -/
  onRpc : Peer → List Nat → BaseIO Unit := fun _ _ => pure ()

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
  /-- The number of refused outbound frames. -/
  dropped : BaseIO Nat

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

/-- The one input queue carries core events and alarm wakes. -/
inductive Input where
  | event (e : Core.Event)
  | wake (now : Millis)

/-- One peer's bounded writer queue and its currently open stream. -/
structure Outbound where
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
closes the stream at the end. A failed write closes the queue and reports
peerLeft. Stop resets an installed stream; a late open checks closing too. -/
private def writer (host : HostSeam) (closing : Conc.OnceRef Bool)
    (events : Conc.Chan Input) (peer : Peer) (ob : Outbound) : Conc.Async Unit := do
  let fail : Conc.Async Unit := do
    (ob.queue.close : BaseIO Unit)
    discard <| events.send (.event (.peerLeft peer))
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

/-- The total frame size once its prefix is complete. A prefix under the
RPC cap can use up to Varint.maxBytes bytes. The decoder checks the length
before the handler appends any body bytes. -/
private def frameSize (buf : ByteArray) : Except Mock.Core.Error (Option Nat) :=
  let head := Bytes.toNatList (buf.extract 0 Varint.maxBytes)
  match Streams.Framing.decodeLength? .uvarint head with
  | .error .truncated => .ok none
  | .error .malformed => .error (.protocol "the RPC prefix is malformed")
  | .ok (size, rest) =>
    if Constants.rpcCap < size then .error (.protocol "the RPC exceeds the cap")
    else .ok (some (head.length - rest.length + size))

/-- Read consecutive frames. The buffer holds only the current frame.
A chunk may hold several frames, so pos marks the bytes already consumed.
The handler appends only the bytes needed by the prefix or current body.
Its buffer stays under the RPC cap plus Varint.maxBytes, even when one
chunk holds many frames. EOF between frames is clean. -/
private partial def readFrames (events : Conc.Chan Input) (peer : Peer)
    (stream : Streams.Stream) (buf chunk : ByteArray) (pos : Nat) :
    Conc.Async (Except Mock.Core.Error Unit) := do
  match frameSize buf with
  | .error e => return .error e
  | .ok size? =>
    if let some size := size? then
      if size ≤ buf.size then
        match Rpc.decodeFrame? (Bytes.toNatList buf) with
        | .ok (some (payload, [])) =>
          -- Park: the loop frees a slot, or stop closes the event queue.
          match ← events.send (.event (.rpc peer payload)) with
          | .error _ => return .ok ()
          | .ok () => return ← readFrames events peer stream ByteArray.empty chunk pos
        | _ => return .error (.protocol "the RPC frame is malformed")
    if pos < chunk.size then
      -- An incomplete prefix needs one byte. A complete prefix fixes the
      -- exact body size, so no append can exceed that frame's bound.
      let need := size?.map (fun size => size - buf.size) |>.getD 1
      let take := Nat.min need (chunk.size - pos)
      readFrames events peer stream (buf ++ chunk.extract pos (pos + take)) chunk (pos + take)
    else
      -- Park: the peer writes, half-closes, or resets.
      match ← stream.read with
      | .error e => return .error (Mock.Core.mapStreamError e)
      | .ok none =>
        return if buf.isEmpty then .ok ()
          else .error (.protocol "the stream ended inside an RPC frame")
      | .ok (some bytes) => readFrames events peer stream buf bytes 0

/-- Serve every RPC of a peer's stream in arrival order. Frame errors reset
both directions. A clean EOF closes our write direction. The host owns and
joins this handler task. -/
def handler (events : Conc.Chan Input) : Mock.Core.StreamHandler where
  id := Constants.meshsubId
  handle peer stream := ExceptT.mk do
    let answer ← readFrames events peer stream ByteArray.empty ByteArray.empty 0
    match answer with
    | .ok () => stream.close
    | .error _ => stream.reset
    return answer

/-! ## The subscription table -/

/-- One delivery callback, with the id that lets `subscribe` take it back. -/
private structure Subscription where
  /-- The id of this registration. -/
  id : Nat
  /-- The topic. -/
  topic : TopicId
  /-- The callback. -/
  callback : Message → BaseIO Unit

/-- The shared table of the callbacks, in registration order. -/
private structure Subscriptions where
  /-- The next free id. -/
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
  /-- The peer writer registry. Only the loop adds entries. -/
  outbound : Conc.OnceRef (List (Peer × Outbound))
  /-- The first stop caller sets this flag. -/
  closing : Conc.OnceRef Bool
  /-- Frames refused by a full or closed outbound queue. -/
  drops : Conc.OnceRef Nat

/-- Encode and offer one RPC to a peer's queue. This operation never parks.
A full queue drops its frame. Each peer has one writer and one stream. -/
private def enqueue (env : Env) (peer : Peer) (rpc : Rpc.RPC) : BaseIO Unit := do
  if ← env.closing.get then return ()
  let some frame := Rpc.encodeFrame? rpc | return ()
  let table ← env.outbound.get
  let ob ← match table.find? (fun e => e.1 == peer) with
    | some (_, ob) => pure ob
    | none => do
      let ob : Outbound := { queue := ← Conc.Chan.new 32, stream := ← Conc.OnceRef.new none }
      env.outbound.update (fun table => (peer, ob) :: table)
      env.tasks.spawn (writer env.host env.closing env.events peer ob)
      pure ob
  if ← env.closing.get then
    ob.queue.close
    return ()
  if !(← ob.queue.trySend (Bytes.ofNatList frame)) then env.drops.update (· + 1)

/-- Retire a peer writer after its disconnect event. -/
private def removePeer (env : Env) (peer : Peer) : BaseIO Unit := do
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

/-- Run the actions of one core step, in order, and answer the delayed
sends. `gossipAt` is the time of the tick when a tick made the actions. The
`i`-th IHAVE send of that tick waits for `trickle i` milliseconds, and every
other action runs now. -/
private def perform (env : Env) (gossipAt : Option Millis)
    (actions : List Core.Action) : BaseIO (List Pending) := do
  let mut delayed : Array Pending := #[]
  let mut gossipIndex := 0
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
            enqueue env to rpc
          else
            delayed := delayed.push { due := now + delay, peer := to, rpc := rpc }
        else
          enqueue env to rpc
      | none => enqueue env to rpc
  return delayed.toList

/-- One core step, then its actions. Only an RPC that does not decode makes
the core answer `.error`. That answer keeps the state, and the loop runs on. -/
private def stepAndAct (env : Env) (st : LoopState) (event : Core.Event) : BaseIO LoopState := do
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
    let gossipAt := match event with
      | .tick now _ => some now
      | _ => none
    let delayed ← perform env gossipAt actions
    return { st with router, pending := st.pending ++ delayed }

/-- Tell every known peer about a subscription change (module doc). -/
private def announce (env : Env) (st : LoopState) (event : Core.Event) :
    BaseIO LoopState := do
  let record? := match event with
    | .subscribe t => some (subOptRpc t true)
    | .unsubscribe t => some (subOptRpc t false)
    | _ => none
  if let some rpc := record? then
    for (peer, _) in st.router.peers do
      enqueue env peer rpc
  return st

/-- The next wake is the first due send or the next heartbeat. -/
private def dueOf (st : LoopState) : Millis :=
  st.pending.foldl (fun due p => Nat.min due p.due) st.nextTick

/-- Send due gossip before the heartbeat shifts the message cache. -/
private def onWake (env : Env) (st : LoopState) (now : Millis) : BaseIO LoopState := do
  let (due, later) := st.pending.partition (fun p => decide (p.due ≤ now))
  for p in due.mergeSort (fun a b => decide (a.due ≤ b.due)) do
    enqueue env p.peer p.rpc
  let st := { st with pending := later }
  if st.nextTick ≤ now then
    let st ← stepAndAct env st (.tick now (st.router.peers.map (·.1)))
    return { st with nextTick := now + env.config.params.heartbeatInterval }
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
      st ← (announce env st e : BaseIO LoopState)
    (env.alarm.set (dueOf st) : BaseIO Unit)
  (env.alarm.close : BaseIO Unit)
  for (_, ob) in ← (env.outbound.get : BaseIO (List (Peer × Outbound))) do
    (ob.queue.close : BaseIO Unit)

/-- The router state of a node with no peers at time `now`. -/
private def initialState (p : Core.Params) (now : Millis) : Core.State :=
  { peers := []
    mesh := []
    fanout := []
    mcache := Cache.MessageCache.empty p.window
    seen := Cache.SeenCache.empty p.seen
    backoff := []
    iwant := []
    topics := []
    now := now
    lastHeartbeat := now }

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
application. -/
def start (host : HostSeam) (config : Config := {}) : BaseIO Node := do
  let now ← config.clock.nowMs
  let subs : Conc.OnceRef Subscriptions ← Conc.OnceRef.new { next := 0, entries := [] }
  let events : Conc.Chan Input ← Conc.Chan.new 64
  host.setHandler (handler events)
  let tasks ← Conc.TaskSet.new
  let alarm ← Conc.Alarm.new
  let outbound ← Conc.OnceRef.new ([] : List (Peer × Outbound))
  let closing ← Conc.OnceRef.new false
  let drops ← Conc.OnceRef.new 0
  tasks.spawn <| alarm.run config.clock (fun now => events.send (.wake now))
  tasks.spawn <| loop { host, config, subs, events, alarm, tasks, outbound, closing, drops }
    { router := initialState config.params now
      pending := []
      nextTick := now + config.params.heartbeatInterval }
  let post : Core.Event → BaseIO Bool := fun e => do
    if ← closing.get then return false
    events.trySend (.event e)
  return {
    publish := fun topic payload => post (.publish (messageOf topic payload))
    subscribe := fun topic callback => do
      if ← closing.get then return false
      -- The cell changes first, so a delivery after the event finds the
      -- callback. A refused event takes this one registration back.
      let id ← subs.updateGet fun s =>
        (s.next,
          { next := s.next + 1
            entries := s.entries ++ [{ id := s.next, topic, callback }] })
      let sent ← post (.subscribe topic)
      if !sent then
        subs.update fun s => { s with entries := s.entries.filter (fun e => e.id != id) }
      return sent
    unsubscribe := fun topic => do
      if ← closing.get then return false
      subs.update fun s => { s with entries := s.entries.filter (fun e => e.topic != topic) }
      post (.unsubscribe topic)
    peerJoined := fun peer proto => post (.peerJoined peer proto)
    peerLeft := fun peer => post (.peerLeft peer)
    dropped := drops.get
    stop := do
      let first ← (closing.updateGet (fun was => (!was, true)) : BaseIO Bool)
      if first then
        (events.close : BaseIO Unit)
        for (_, ob) in ← (outbound.get : BaseIO (List (Peer × Outbound))) do
          endOutbound ob
        tasks.joinAll }

end Libp2p.Protocols.Gossipsub.Node
