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

One task owns the router state. A bounded `Chan` carries the events of the
application and the host. The clock seam carries the heartbeat and the
delayed gossip. The loop parks in `select` over the two, so the timer costs
no task, and a `TestClock` drives every time decision of a test.

`loop` and `readFrames` are `partial`. A peer controls the number of events
and chunks. No measure bounds the wait for a complete frame or a close
(root CLAUDE.md, "`partial def`").

## Ownership

The task set of the node owns the loop task, and `stop` joins it. The host
owns the handler tasks of the inbound streams. Nothing cancels a task:
`stop` closes the event queue, and the close wakes the parked loop. The
router state and the pending gossip are local to the loop, so no cell
guards them. The subscription table is the one shared cell, and it changes
through `OnceRef.update` (root ARCHITECTURE §4.1).

## Recorded decisions

- **The stop field runs in Async.** The brief gives it a BaseIO type.
  TaskSet.joinAll runs in Async, because joining can park. This field keeps
  that type and leaves the blocking run to the application edge.
- **Actions return the next stream table and pending sends.** This follows
  the yamux performAll discipline. These actions use Async because opening
  and writing streams can park. The loop assigns each returned state.
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
- **The default gossip delay is zero.** The pinned go implementation flushes
  heartbeat gossip at once. Config.trickle keeps an explicit delay for tests
  and callers that need one, as section 12 of the brief records.
- **The loop keeps one outbound stream per peer.** Each action returns the
  updated stream table. The loop closes the streams when it ends, and resets
  a stream when its peer leaves or a write fails. The next send can reopen it.
  Opening and writing run on the loop task, so either call can park the loop.
- **The inbound handler serves consecutive frames.** Go and rust keep their
  outbound stream open. The handler bounds each frame before appending bytes,
  and serves several frames from one chunk in order.
- **The receipt observer runs before the core step.** Config.onRpc receives
  the sender and payload bytes of every RPC, including duplicates and bad
  protobuf bodies. Frame errors fail the handler before they reach it.
- **The host posts `peerJoined` before it serves a stream of that peer.** The
  core ignores an RPC from an unknown peer (`Core.rpcStep`), so an earlier
  stream loses its RPC.
- **A send failure has no sink.** The send retires the stream, and the mock host has
  no failure log. The host reports stream failures at integration.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Node

open Mock.Host (HostSeam)

/-- The default sends heartbeat gossip at once, as the pinned go router does.
Callers can provide a delay through Config.trickle. -/
def defaultTrickle (_i : Nat) : Millis := 0

/-- The configuration of one node: the router parameters, the clock the
loop reads, and the spread of the heartbeat gossip. -/
structure Config where
  /-- The router parameters. -/
  params : Core.Params := Core.defaults
  /-- The clock of the loop's timer. -/
  clock : Conc.Clock := Conc.Clock.system
  /-- The delay of the `i`-th gossip send of one heartbeat, in milliseconds.
  The caller fixes it, so a test gets exact times. -/
  trickle : Nat → Millis := defaultTrickle
  /-- Observe each inbound RPC before validation and deduplication. The callback
  runs on the loop task and must not park. The bytes are the unframed body. -/
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

/-- The outbound streams owned by the loop, one per peer. Each send returns
its next table, so the loop assigns from the answer. -/
abbrev Outbound := List (Peer × Streams.Stream)

/-- Retire a peer's outbound stream. Reset wakes both directions. -/
private def retire (streams : Outbound) (peer : Peer) : Conc.Async Outbound := do
  for (p, stream) in streams do
    if p = peer then stream.reset
  return streams.filter (fun e => e.1 != peer)

/-- Write one frame and return the stream table. A successful write keeps
its stream open. A failed write resets and removes it. -/
private def writeFrame (streams : Outbound) (peer : Peer) (stream : Streams.Stream)
    (frame : List Nat) : Conc.Async Outbound := do
  try
    match ← stream.write (Bytes.ofNatList frame) with
    | .ok () => return streams
    | .error _ => retire streams peer
  catch _ => retire streams peer

/-- Send one RPC through the peer's stream and return the next stream table.
An RPC over Constants.rpcCap opens no stream. A failed open leaves the table
unchanged. The host reports send failures at integration. -/
def sendRpc (host : HostSeam) (streams : Outbound) (to : Peer) (rpc : Rpc.RPC) :
    Conc.Async Outbound := do
  let some frame := Rpc.encodeFrame? rpc | return streams
  if let some (_, stream) := streams.find? (fun e => e.1 == to) then
    return ← writeFrame streams to stream frame
  try
    match ← host.newStream to [Constants.meshsubId] with
    | .error _ => return streams
    | .ok (_, stream) => writeFrame ((to, stream) :: streams) to stream frame
  catch _ => return streams

/-- Half-close each outbound stream when the loop ends. The peer's read
wakes at EOF, and its host joins the inbound handler. -/
private def closeOutbound (streams : Outbound) : Conc.Async Unit := do
  for (_, stream) in streams do
    stream.close

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
private partial def readFrames (events : Conc.Chan Core.Event) (peer : Peer)
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
          match ← events.send (.rpc peer payload) with
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
def handler (events : Conc.Chan Core.Event) : Mock.Core.StreamHandler where
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
  events : Conc.Chan Core.Event

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
  /-- The outbound streams owned by this loop. -/
  streams : Outbound
  /-- The gossip sends that wait for their due time. -/
  pending : List Pending
  /-- The time of the next heartbeat. -/
  nextTick : Millis

/-- What wakes the loop: the timer, or the event queue. `none` is a closed
and empty queue. -/
private inductive Wake where
  | timer
  | event (e : Option Core.Event)

/-- Run the actions of one core step, in order, and answer the delayed
sends. `gossipAt` is the time of the tick when a tick made the actions. The
`i`-th IHAVE send of that tick waits for `trickle i` milliseconds, and every
other action runs now. -/
private def perform (env : Env) (streams : Outbound) (gossipAt : Option Millis)
    (actions : List Core.Action) : Conc.Async (Outbound × List Pending) := do
  let mut streams := streams
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
            streams ← sendRpc env.host streams to rpc
          else
            delayed := delayed.push { due := now + delay, peer := to, rpc := rpc }
        else
          streams ← sendRpc env.host streams to rpc
      | none => streams ← sendRpc env.host streams to rpc
  return (streams, delayed.toList)

/-- One core step, then its actions. Only an RPC that does not decode makes
the core answer `.error`. That answer keeps the state, and the loop runs on. -/
private def stepAndAct (env : Env) (st : LoopState) (event : Core.Event) : Conc.Async LoopState := do
  if let .rpc peer bytes := event then
    (env.config.onRpc peer bytes : BaseIO Unit)
  let st ← match event with
    | .peerLeft peer => do
      let streams ← retire st.streams peer
      pure { st with streams, pending := st.pending.filter (fun p => p.peer != peer) }
    | _ => pure st
  match Core.step env.config.params st.router event with
  | .error (.decode _) => return st
  | .ok (router, actions) =>
    let gossipAt := match event with
      | .tick now _ => some now
      | _ => none
    let (streams, delayed) ← perform env st.streams gossipAt actions
    return { st with router, streams, pending := st.pending ++ delayed }

/-- Tell every known peer about a subscription change (module doc). -/
private def announce (env : Env) (st : LoopState) (event : Core.Event) :
    Conc.Async LoopState := do
  let record? := match event with
    | .subscribe t => some (subOptRpc t true)
    | .unsubscribe t => some (subOptRpc t false)
    | _ => none
  let mut streams := st.streams
  if let some rpc := record? then
    for (peer, _) in st.router.peers do
      streams ← sendRpc env.host streams peer rpc
  return { st with streams }

/-- The loop. Each pass sends the gossip that came due, runs the heartbeat
when it came due, arms one timer for the next due time, and parks.

A due time in the past gives a timer of 0 ms: the `Nat` subtraction stops at
0, and such a timer completes at once. The tick runs at the top of the pass,
so an event queue that stays full cannot hold a heartbeat back. The peer
order of a tick comes from the state of the loop, its only writer. -/
private partial def loop (env : Env) (st : LoopState) : Conc.Async Unit := do
  let clock := env.config.clock
  -- The ascription marks the action `BaseIO`, so the lift into `Async` applies
  -- (see `Conc.TaskSet.joinAll`).
  let now ← (clock.nowMs : BaseIO Nat)
  let (due, later) := st.pending.partition (fun p => decide (p.due ≤ now))
  let mut streams := st.streams
  for p in due.mergeSort (fun a b => decide (a.due ≤ b.due)) do
    streams ← sendRpc env.host streams p.peer p.rpc
  let st : LoopState := { st with streams, pending := later }
  let st ←
    if st.nextTick ≤ now then do
      let order := st.router.peers.map (·.1)
      let st ← stepAndAct env st (.tick now order)
      pure { st with nextTick := now + env.config.params.heartbeatInterval }
    else
      pure st
  let wake := st.pending.foldl (fun m p => Nat.min m p.due) st.nextTick
  let timer ← (clock.after (wake - now) : BaseIO (Conc.Park Unit))
  -- Park: a send or a close of the queue wakes it, and so does the timer.
  match ← Conc.select #[Conc.Park.recv env.events Wake.event, timer.map fun () => Wake.timer] with
  | .timer => loop env st
  | .event none => closeOutbound st.streams
  | .event (some e) =>
    let st ← stepAndAct env st e
    let st ← announce env st e
    loop env st

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
  let events : Conc.Chan Core.Event ← Conc.Chan.new 64
  host.setHandler (handler events)
  let tasks ← Conc.TaskSet.new
  tasks.spawn <| loop { host, config, subs, events }
    { router := initialState config.params now
      streams := []
      pending := []
      nextTick := now + config.params.heartbeatInterval }
  return {
    publish := fun topic payload => events.trySend (.publish (messageOf topic payload))
    subscribe := fun topic callback => do
      -- The cell changes first, so a delivery after the event finds the
      -- callback. A refused event takes this one registration back.
      let id ← subs.updateGet fun s =>
        (s.next,
          { next := s.next + 1
            entries := s.entries ++ [{ id := s.next, topic, callback }] })
      let sent ← events.trySend (.subscribe topic)
      if !sent then
        subs.update fun s => { s with entries := s.entries.filter (fun e => e.id != id) }
      return sent
    unsubscribe := fun topic => do
      subs.update fun s => { s with entries := s.entries.filter (fun e => e.topic != topic) }
      events.trySend (.unsubscribe topic)
    peerJoined := fun peer proto => events.trySend (.peerJoined peer proto)
    peerLeft := fun peer => events.trySend (.peerLeft peer)
    stop := do
      (events.close : BaseIO Unit)
      tasks.joinAll }

end Libp2p.Protocols.Gossipsub.Node
