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

`loop` and `readFrames` are `partial`. Each runs until a close reaches what
it parks on, and no measure bounds the number of events or chunks before
that close (root CLAUDE.md, "`partial def`").

## Ownership

The task set of the node owns the loop task, and `stop` joins it. The host
owns the handler tasks of the inbound streams. Nothing cancels a task:
`stop` closes the event queue, and the close wakes the parked loop. The
router state and the pending gossip are local to the loop, so no cell
guards them. The subscription table is the one shared cell, and it changes
through `OnceRef.update` (root ARCHITECTURE §4.1).

## Recorded decisions

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
- **The gossip spread is fixed.** The go implementation draws the delay of
  its gossip from a random source. `defaultTrickle` is a fixed function, so a
  run replays exactly. The tolerance of the unit 3c gate on latency is an
  open question on the pull request. The peer order of a tick is the order
  of the state, for the same reason.
- **One outbound stream per RPC.** `sendRpc` opens a stream, writes one frame,
  and half-closes it. A send runs on the loop task, so a host whose
  `newStream` parks also parks the loop. Two RPCs to one peer can reorder,
  because each stream has its own handler task. The unit 3c gate decides if
  this shape stays.
- **The inbound handler reads frames until the end of the stream.** A peer
  that keeps one stream open and writes many frames gets every frame served.
- **The host posts `peerJoined` before it serves a stream of that peer.** The
  core ignores an RPC from an unknown peer (`Core.rpcStep`), so an earlier
  stream loses its RPC.
- **A send failure has no sink.** `sendRpc` answers `Unit`, and the mock host has
  no failure log. The host reports stream failures at integration.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Node

open Mock.Host (HostSeam)

/-- The delay of the `i`-th gossip send of a heartbeat: a fixed spread below
one second, so two nodes do not line up and a run replays. The multiplier
is a prime, so the delays do not repeat with a short period. -/
def defaultTrickle (i : Nat) : Millis :=
  (i * 7919 + 1) % 1000

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

/-- Send one RPC on a new stream, and half-close the stream. An RPC over
`Constants.rpcCap` is never sent. Every failure ends this send and leaves
the loop running, and the module doc records why nothing reports it. -/
def sendRpc (host : HostSeam) (to : Peer) (rpc : Rpc.RPC) : Conc.Async Unit := do
  let some frame := Rpc.encodeFrame? rpc | return ()
  try
    match ← host.newStream to [Constants.meshsubId] with
    | .error _ => return ()
    | .ok (_, stream) =>
      match ← stream.write (Bytes.ofNatList frame) with
      | .ok () => stream.close
      | .error _ => stream.reset
  catch _ =>
    return ()

/-! ## The inbound handler -/

/-- The bytes of `buf` from `pos` that `Rpc.decodeFrame?` needs for its answer.
`none` asks for another chunk.

The prefix decides, so the decoder reads each frame once, and a peer that
sends many small chunks costs no repeated decode. A length over the cap, or
a bad prefix, needs only the prefix bytes. So the handler keeps at most one
frame under the cap and one chunk (root ARCHITECTURE §5.1). -/
private def frameWindow (buf : ByteArray) (pos : Nat) : Option Nat :=
  let head := Bytes.toNatList (buf.extract pos (pos + Varint.maxBytes))
  match Streams.Framing.decodeLength? .uvarint head with
  | .ok (len, rest) =>
    let whole := (head.length - rest.length) + len
    if Constants.rpcCap < len then some head.length
    else if pos + whole ≤ buf.size then some whole
    else none
  | .error .truncated => none
  | .error .malformed => some head.length

/-- Post every frame of the stream to the queue, until the stream ends.

`pos` is the start of the next frame in `buf`, so a chunk that holds many
frames costs one pass over its bytes. The answer is `.error` for a bad frame,
for an end of stream inside a frame, and for a failed read. A closed queue
means the node stops, and the handler returns. -/
private partial def readFrames (events : Conc.Chan Core.Event) (peer : Peer)
    (stream : Streams.Stream) (buf : ByteArray) (pos : Nat) :
    Conc.Async (Except Mock.Core.Error Unit) := do
  match frameWindow buf pos with
  | some n =>
    match Rpc.decodeFrame? (Bytes.toNatList (buf.extract pos (pos + n))) with
    | .ok (some (payload, _)) =>
      -- Park: the loop frees a slot, or `stop` closes the queue. The window
      -- holds one frame, so the rest is empty and the next frame starts at
      -- `pos + n`.
      match ← events.send (.rpc peer payload) with
      | .ok () => readFrames events peer stream buf (pos + n)
      | .error _ => return .ok ()
    | .ok none => return .error (.protocol "the RPC frame ended early")
    | .error _ => return .error (.protocol "the RPC frame is malformed")
  | none =>
    -- Park: the peer writes, half-closes, or resets.
    match ← stream.read with
    | .error e => return .error (Mock.Core.mapStreamError e)
    | .ok none =>
      return if pos = buf.size then .ok ()
        else .error (.protocol "the stream ended inside an RPC frame")
    | .ok (some chunk) => readFrames events peer stream (buf.extract pos buf.size ++ chunk) 0

/-- The handler of `Constants.meshsubId`. Each frame becomes one `Event.rpc`
with the opener of the stream as its sender. A protocol error resets the
stream and fails this handler. The loop keeps running. -/
def handler (events : Conc.Chan Core.Event) : Mock.Core.StreamHandler where
  id := Constants.meshsubId
  handle peer stream := ExceptT.mk do
    let answer ← readFrames events peer stream ByteArray.empty 0
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
private def perform (env : Env) (gossipAt : Option Millis) (actions : List Core.Action) :
    Conc.Async (List Pending) := do
  let mut delayed : Array Pending := #[]
  for action in actions do
    match action with
    | .deliver m => (deliver env.subs m : BaseIO Unit)
    | .sendRpc to rpc =>
      match gossipAt with
      | some now =>
        if hasIhave rpc then
          delayed := delayed.push
            { due := now + env.config.trickle delayed.size, peer := to, rpc := rpc }
        else
          sendRpc env.host to rpc
      | none => sendRpc env.host to rpc
  return delayed.toList

/-- One core step, then its actions. Only an RPC that does not decode makes
the core answer `.error`. That answer keeps the state, and the loop runs on. -/
private def stepAndAct (env : Env) (st : LoopState) (event : Core.Event) : Conc.Async LoopState := do
  match Core.step env.config.params st.router event with
  | .error (.decode _) => return st
  | .ok (router, actions) =>
    let gossipAt := match event with
      | .tick now _ => some now
      | _ => none
    let delayed ← perform env gossipAt actions
    return { st with router, pending := st.pending ++ delayed }

/-- Tell every known peer about a subscription change (module doc). -/
private def announce (env : Env) (router : Core.State) : Core.Event → Conc.Async Unit
  | .subscribe t => do
    for (peer, _) in router.peers do
      sendRpc env.host peer (subOptRpc t true)
  | .unsubscribe t => do
    for (peer, _) in router.peers do
      sendRpc env.host peer (subOptRpc t false)
  | _ => return ()

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
  for p in due.mergeSort (fun a b => decide (a.due ≤ b.due)) do
    sendRpc env.host p.peer p.rpc
  let st : LoopState := { st with pending := later }
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
  | .event none => return ()
  | .event (some e) =>
    let st ← stepAndAct env st e
    announce env st.router e
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
