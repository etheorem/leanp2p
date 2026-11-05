import Libp2p.Protocols.Gossipsub.Types
import Libp2p.Protocols.Gossipsub.Rpc
import Libp2p.Protocols.Gossipsub.Score
import Libp2p.Protocols.Gossipsub.Cache
import Libp2p.Protocols.Gossipsub.Sign

/-!
# Gossipsub router core

The pure state machine of the gossipsub v1.1 router: the state, the
external events, the outgoing actions, the one error constructor, and
the total `step`. Time and the peer order enter as event data, so the
core reads no clock and makes no random choice. `run` drives a list of
events.

The core owns the mesh, the fanout, the score accounting, and the
heartbeat. It calls the public surface of the score, the cache, and the
sign parts. It decodes an inbound RPC at its own boundary and maps a
decode failure to the one error constructor.

An inbound message that passes validation and is not already seen is
delivered to the application and forwarded to every other peer of
`mesh[topic]`. The sender already holds it, so the forward list drops
the sender. A local publish records the message id in the seen cache,
so a later echo of the same id is not forwarded again.

The heartbeat emits gossip after it settles the mesh and before it
shifts the message cache. The recipients are peers of the supplied order
at or above the gossip threshold that are in neither the mesh nor the
fanout of the topic, up to `dLazy` per topic. `gossipFactor` is stored
and never read, so the emission count is not adaptive.

Several fields of the spec are stored and never read, and several
behaviors are absent:

- `PubsubProto` is stored and no path reads it, so floodsub peers are
  not a separate forward set.
- `ControlPrune.peers` decodes and `handlePrune` ignores it, so peer
  exchange is absent. `acceptPXThreshold` is never read.
- `opportunisticGraftThreshold` is never read.
- `fanoutTtl` is never read, so a fanout entry does not expire.
- `handleIhave` records a promise and nothing calls
  `PromiseTable.broken`, so an expired promise changes no score.
- No event writes `appScore`, `ipColocation`, or `behaviourPenalty`, so
  P5, P6, and P7 have no producer. `PeerData` carries no address.
- `meshMessageDeliveriesWindow` is never read. A mesh peer counts
  toward P3 for every accepted message.
- `leave` deletes the peer record, so a score does not survive a
  disconnect.
- `planTopic` drops the oldest mesh entries. `dScore` is never read and
  there is no outbound flag, so the `D_out` quota is absent.
- `validationOk` uses `strictNoSign`. There is no per-topic policy and
  no Ignore outcome. `defaults.msgId` is the payload, because that
  policy leaves `from` and `seqno` absent and the spec's default id
  would be empty for every accepted message.
- IHAVE and IWANT caps and flood publishing are absent.
  `publishThreshold` is stored and never read.
- A graft for a topic the router does not subscribe to is ignored. The
  v1.0 spec answers with a prune, and the v1.1 spam measures say to
  ignore it. This step follows v1.1.
- `unsubscribe` writes `pruneBackoff`. The spec's shorter unsubscribe
  backoff is absent, and `subscribe` does not consult the backoff.

The spec sections are `vendor/specs/pubsub/gossipsub/gossipsub-v1.0.md`
(the router, the message cache, the mesh, the fanout, the heartbeat) and
`gossipsub-v1.1.md` (the score gates, the backoff, the spam measures).
The root `docs/ARCHITECTURE.md` section 3.3 fixes the shape: one total
`step` that returns `Except ProtocolError (State × List Action)`, with
time as an input.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Core

open Libp2p.Protocols.Gossipsub

/-! ## Types -/

/-- The pubsub protocol a peer negotiated. -/
inductive PubsubProto where
  /-- The gossipsub mesh protocol. -/
  | meshsub
  /-- The floodsub protocol. -/
  | floodsub
  deriving DecidableEq, BEq, Repr

/-- The per-peer record: the score state, the pubsub protocol, and the
topics the peer announced. `Peer` keeps its one meaning, the peer id of
`Types.lean`. -/
structure PeerData where
  /-- The score state of the peer. -/
  score : Score.PeerState
  /-- The pubsub protocol of the peer. -/
  proto : PubsubProto
  /-- The announced topics. -/
  subs : List TopicId

/-- The mesh degree parameters: `d`, `dLow`, `dHigh`, `dScore`, `dLazy`. -/
structure MeshParams where
  /-- The target mesh degree. -/
  d : Nat
  /-- The low mesh water mark. -/
  dLow : Nat
  /-- The high mesh water mark. -/
  dHigh : Nat
  /-- The number of score-best peers the mesh keeps. -/
  dScore : Nat
  /-- The number of peers that receive gossip. -/
  dLazy : Nat
  deriving DecidableEq, Repr

/-- The router parameters. -/
structure Params where
  /-- The score parameters. -/
  score : Score.Params
  /-- The score thresholds. -/
  thresholds : Thresholds
  /-- The mesh degree parameters. -/
  mesh : MeshParams
  /-- The heartbeat interval in milliseconds. -/
  heartbeatInterval : Millis
  /-- The fanout time to live in milliseconds. -/
  fanoutTtl : Millis
  /-- The prune backoff period in milliseconds. -/
  pruneBackoff : Millis
  /-- The gossip factor in percent. -/
  gossipFactor : Nat
  /-- The IWANT answer deadline in milliseconds. -/
  iwantDeadline : Millis
  /-- The message cache window parameters. -/
  window : Cache.WindowParams
  /-- The seen cache parameters. -/
  seen : Cache.SeenParams
  /-- The signature primitives. -/
  prims : Sign.Prims
  /-- The message id function. -/
  msgId : Sign.MsgIdFn

/-- The parameter bound the mesh theorems consume: the target degree is
at most the high water mark. -/
structure Params.Valid (p : Params) : Prop where
  /-- The target degree is at most the high water mark. -/
  d_le_dHigh : p.mesh.d ≤ p.mesh.dHigh

/-- One fanout record: the peers and the last publish time. -/
structure Fanout where
  /-- The fanout peers. -/
  peers : List Peer
  /-- The last publish time. -/
  lastPublished : Millis
  deriving Repr

/-- The router state. -/
structure State where
  /-- The known peers and their records. -/
  peers : List (Peer × PeerData)
  /-- The mesh of each topic. -/
  mesh : List (TopicId × List Peer)
  /-- The fanout of each topic. -/
  fanout : List (TopicId × Fanout)
  /-- The message cache. -/
  mcache : Cache.MessageCache
  /-- The seen cache. -/
  seen : Cache.SeenCache
  /-- The backoff table. -/
  backoff : Cache.BackoffTable
  /-- The IWANT promises. -/
  iwant : Cache.PromiseTable
  /-- The topics the router subscribes to. -/
  topics : List TopicId
  /-- The current time. -/
  now : Millis
  /-- The time of the last heartbeat. -/
  lastHeartbeat : Millis

/-- The external events. -/
inductive Event where
  /-- A peer joined with a protocol. -/
  | peerJoined (peer : Peer) (proto : PubsubProto)
  /-- A peer left. -/
  | peerLeft (peer : Peer)
  /-- An RPC arrived from a peer, as bytes. -/
  | rpc (sender : Peer) (bytes : List Nat)
  /-- The application publishes a message. -/
  | publish (msg : Message)
  /-- The application subscribes to a topic. -/
  | subscribe (topic : TopicId)
  /-- The application unsubscribes from a topic. -/
  | unsubscribe (topic : TopicId)
  /-- The heartbeat fires at `now` with a peer order. -/
  | tick (now : Millis) (order : List Peer)
  deriving Repr

/-- The outgoing actions. -/
inductive Action where
  /-- Send an RPC to a peer. -/
  | sendRpc (to : Peer) (rpc : Rpc.RPC)
  /-- Deliver a message to the application. -/
  | deliver (msg : Message)
  deriving DecidableEq, BEq, Repr

/-- The one error constructor: an RPC that does not decode. -/
inductive ProtocolError where
  /-- The RPC bytes do not decode. -/
  | decode (e : Pb.Error)
  deriving DecidableEq, BEq, Repr

/-! ## Boolean membership -/

/-- Boolean membership, decided by `DecidableEq`. The core uses it in
the guards of its definitions, because a `Prop` membership has no
decidable instance in the core library. -/
def memB {α : Type} [DecidableEq α] (a : α) (l : List α) : Bool :=
  l.any (fun b => decide (b = a))

/-- The Boolean membership holds exactly for the `Prop` membership. -/
theorem memB_eq_true {α : Type} [DecidableEq α] {a : α} {l : List α} :
    memB a l = true ↔ a ∈ l := by
  rw [memB, List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hab⟩
    rw [← of_decide_eq_true hab]
    exact hb
  · intro h
    exact ⟨a, h, by simp⟩

/-! ## Association list accessors -/

/-- The first list of the topic. -/
def lookupTopic : List (TopicId × List Peer) → TopicId → List Peer
  | [], _ => []
  | (t', ps) :: l, t => if t = t' then ps else lookupTopic l t

/-- Replace the first entry of the topic, or append the topic. -/
def upsertMesh : List (TopicId × List Peer) → TopicId → List Peer →
    List (TopicId × List Peer)
  | [], t, ps => [(t, ps)]
  | (t', ps') :: l, t, ps => if t = t' then (t, ps) :: l else (t', ps') :: upsertMesh l t ps

/-- The mesh of the topic. -/
def meshOf (s : State) (topic : TopicId) : List Peer := lookupTopic s.mesh topic

/-- Write the mesh of the topic. -/
def setTopicMesh (s : State) (topic : TopicId) (ps : List Peer) : State :=
  { s with mesh := upsertMesh s.mesh topic ps }

/-- The first fanout record of the topic. -/
def lookupFanout : List (TopicId × Fanout) → TopicId → Option Fanout
  | [], _ => none
  | (t', f) :: l, t => if t = t' then some f else lookupFanout l t

/-- The fanout peers of the topic. -/
def fanoutOf (s : State) (topic : TopicId) : List Peer :=
  match lookupFanout s.fanout topic with
  | some f => f.peers
  | none => []

/-- Write the fanout record of the topic. -/
def setTopicFanout (s : State) (topic : TopicId) (f : Fanout) : State :=
  { s with fanout := (topic, f) :: s.fanout.filter (fun e => decide (e.1 ≠ topic)) }

/-- The first record of the peer. -/
def lookupPeer : List (Peer × PeerData) → Peer → Option PeerData
  | [], _ => none
  | (q', pd) :: l, q => if q = q' then some pd else lookupPeer l q

/-- Replace the first record of the peer, or append the peer. -/
def upsertPeer : List (Peer × PeerData) → Peer → PeerData → List (Peer × PeerData)
  | [], q, pd => [(q, pd)]
  | (q', pd') :: l, q, pd => if q = q' then (q, pd) :: l else (q', pd') :: upsertPeer l q pd

/-- The record of the peer. -/
def peerOf (s : State) (q : Peer) : Option PeerData := lookupPeer s.peers q

/-- Write the record of the peer. -/
def setPeer (s : State) (q : Peer) (pd : PeerData) : State :=
  { s with peers := upsertPeer s.peers q pd }

/-- Update every peer record through `f`. The list order stays. -/
def mapPeers (s : State) (f : Peer → PeerData → PeerData) : State :=
  { s with peers := s.peers.map (fun e => (e.1, f e.1 e.2)) }

/-- Update the score state of one peer and leave every other field. -/
def updateScoreOf (s : State) (q : Peer) (f : Score.PeerState → Score.PeerState) : State :=
  mapPeers s (fun r pd => if r = q then { pd with score := f pd.score } else pd)

/-- The score of a peer at the state time. A missing peer scores 0. -/
def scoreOf (p : Params) (s : State) (q : Peer) : Score :=
  match peerOf s q with
  | some pd => Score.score p.score pd.score s.now
  | none => 0

/-- The next heartbeat is due: the interval has passed since the last one. -/
def heartbeatDue (p : Params) (s : State) (now : Millis) : Prop :=
  s.lastHeartbeat + p.heartbeatInterval ≤ now

/-- The heartbeat condition is decidable. -/
instance heartbeatDueDecidable (p : Params) (s : State) (now : Millis) :
    Decidable (heartbeatDue p s now) :=
  decidable_of_iff (s.lastHeartbeat + p.heartbeatInterval ≤ now) Iff.rfl

/-- The RPC grafts the topic. -/
def rpcGrafts (r : Rpc.RPC) (t : TopicId) : Prop :=
  match r.control with
  | some c => ∃ g ∈ c.graft, g.topicId = t.name
  | none => False

/-- The RPC prunes the topic. -/
def rpcPrunes (r : Rpc.RPC) (t : TopicId) : Prop :=
  match r.control with
  | some c => ∃ p ∈ c.prune, p.topicId = t.name
  | none => False

/-- The RPC carries nonempty ihave gossip. -/
def rpcHasIhave (r : Rpc.RPC) : Prop :=
  match r.control with
  | some c => c.ihave ≠ []
  | none => False

/-- The messages the action list delivers to the application. -/
def delivers : List Action → List Message
  | [] => []
  | .deliver m :: as => m :: delivers as
  | .sendRpc _ _ :: as => delivers as

/-! ## Outgoing RPC constructors -/

/-- An RPC that carries one control message. -/
def controlRpc (c : Rpc.ControlMessage) : Rpc.RPC :=
  { subscriptions := [], publish := [], control := some c }

/-- The hello RPC: one subscription record per topic. -/
def helloRpc (topics : List TopicId) : Rpc.RPC :=
  { subscriptions := topics.map (fun t => ({ subscribe := true, topicid := t.name } : Rpc.SubOpts)),
    publish := [], control := none }

/-- A graft of the topic. -/
def graftRpc (t : TopicId) : Rpc.RPC :=
  controlRpc { ihave := [], iwant := [], graft := [{ topicId := t.name }], prune := [] }

/-- A prune of the topic with the backoff period in seconds. -/
def pruneRpc (t : TopicId) (backoff : Millis) : Rpc.RPC :=
  controlRpc
    { ihave := [], iwant := [], graft := [],
      prune := [{ topicId := t.name, peers := [], backoff := some (backoff / 1000) }] }

/-- An IHAVE of the topic with the message ids. -/
def ihaveRpc (t : TopicId) (ids : List MessageId) : Rpc.RPC :=
  controlRpc
    { ihave := [{ topicId := t.name, messageIds := ids }], iwant := [], graft := [], prune := [] }

/-- An IWANT with the message ids. -/
def iwantRpc (ids : List MessageId) : Rpc.RPC :=
  controlRpc { ihave := [], iwant := [{ messageIds := ids }], graft := [], prune := [] }

/-- An RPC that forwards one published message. -/
def publishRpc (m : Message) : Rpc.RPC :=
  { subscriptions := [], publish := [m], control := none }

/-- The mesh peers that receive a forwarded inbound message. The sender
already holds the message, so the list drops the sender. -/
def inboundTargets (s : State) (sender : Peer) (topic : TopicId) : List Peer :=
  (meshOf s topic).filter (fun q => decide (q ≠ sender))

/-- One publish RPC per accepted message, to each mesh peer other than
the sender. The targets are read from the pre-state mesh. -/
def forwardPubs (s : State) (sender : Peer) (ms : List Message) : List Action :=
  ms.flatMap fun m =>
    (inboundTargets s sender m.topic).map fun q => Action.sendRpc q (publishRpc m)

/-! ## The decode boundary -/

/-- The one decode entry point of the core: wire bytes to an RPC value.
The protobuf decoder returns the empty suffix, so the core drops it. -/
def decodeRpc (bytes : List Nat) : Except ProtocolError Rpc.RPC :=
  match Pb.decodeMessage? (α := Rpc.RPC) bytes with
  | .ok (r, _) => .ok r
  | .error e => .error (.decode e)

/-- A decode that the model decoder reports as successful decodes to the
same value. -/
theorem decodeRpc_of_decodeMessage (bytes : List Nat) (r : Rpc.RPC)
    (h : Pb.decodeMessage? (α := Rpc.RPC) bytes = .ok (r, [])) :
    decodeRpc bytes = .ok r := by
  simp [decodeRpc, h]

/-- A `strictNoSign` validation as a `Bool`. -/
def validationOk (p : Params) (m : Message) : Bool :=
  match Sign.validate p.prims (fun x => Pb.encodeMessage x) .strictNoSign m with
  | .ok _ => true
  | .error _ => false

/-! ## Message acceptance -/

/-- One run of the acceptance loop: the accepted messages, the ids the
loop saw, and the seen cache after the run. -/
structure Accept where
  /-- The accepted messages, in arrival order. -/
  accepted : List Message
  /-- The ids the loop passed. -/
  done : List MessageId
  /-- The seen cache after the run. -/
  cache : Cache.SeenCache

/-- Accept a list of messages. The gate reads the pre-state cache `c0`,
so a message that the pre-state cache holds as seen is never accepted.
The local `done` list rejects a repeated id inside the one event. -/
def accept (c0 : Cache.SeenCache) (now : Millis) (idf : Sign.MsgIdFn)
    (done : List MessageId) (c : Cache.SeenCache) : List Message → Accept
  | [] => { accepted := [], done := done, cache := c }
  | m :: ms =>
      if c0.contains (idf m) now || memB (idf m) done then
        accept c0 now idf done c ms
      else
        let r := accept c0 now idf (idf m :: done) (c.add (idf m) now) ms
        { accepted := m :: r.accepted, done := r.done, cache := r.cache }

/-! ## The heartbeat plan -/

/-- One per-topic heartbeat plan: the kept mesh, the pruned peers, and
the added peers. -/
structure TopicPlan where
  /-- The topic. -/
  topic : TopicId
  /-- The mesh after the heartbeat. -/
  kept : List Peer
  /-- The peers that leave the mesh. -/
  pruned : List Peer
  /-- The peers that enter the mesh. -/
  added : List Peer
  deriving Repr

/-- The peers that announce the topic. -/
def announced (s : State) (topic : TopicId) : List Peer :=
  (s.peers.filter (fun e => memB topic e.2.subs)).map Prod.fst

/-- One topic plan. An overfull mesh drops its oldest entries down to
`d`, an underfull mesh takes candidates from the order up to `d`, and a
candidate is outside the mesh, outside backoff, known, and at or above
score 0. The kept list is cut at `dHigh`, so the mesh bound holds by
construction. -/
def planTopic (p : Params) (s : State) (now : Millis) (order : List Peer)
    (topic : TopicId) : TopicPlan :=
  let ps := meshOf s topic
  let excess := if ps.length > p.mesh.dHigh then ps.length - p.mesh.d else 0
  let over := ps.take excess
  let kept0 := ps.drop excess
  let need := if kept0.length < p.mesh.dLow then p.mesh.d - kept0.length else 0
  let cands := order.filter (fun q =>
    !memB q ps && !(Cache.Backoff.active s.backoff q topic now) &&
      (peerOf s q).isSome && decide (0 ≤ scoreOf p s q))
  let added := cands.take need
  { topic := topic, kept := (kept0 ++ added).take p.mesh.dHigh, pruned := over, added := added }

/-- The plan of every topic in the mesh. -/
def planList (p : Params) (s : State) (now : Millis) (order : List Peer) : List TopicPlan :=
  s.mesh.map (fun e => planTopic p s now order e.1)

/-- Apply the score updates of the plans: a pruned peer takes the prune
update, an added peer takes the graft update. -/
def applyPlanScores (p : Params) (s : State) (plans : List TopicPlan) : State :=
  mapPeers s (fun q pd =>
    { pd with
      score := plans.foldl (fun sc pl =>
        if memB q pl.pruned then Score.prune p.score sc s.now pl.topic
        else if memB q pl.added then Score.graft sc s.now pl.topic
        else sc) pd.score })

/-- The actions of the plans: a prune to each pruned peer, then a graft
to each added peer. -/
def planActions (p : Params) (pl : TopicPlan) : List Action :=
  pl.pruned.map (fun q => Action.sendRpc q (pruneRpc pl.topic p.pruneBackoff)) ++
    pl.added.map (fun q => Action.sendRpc q (graftRpc pl.topic))

/-- Write the planned meshes and drop the peers below score 0 from every
mesh. A dropped peer takes the prune score update. -/
def settleMesh (p : Params) (s : State) (plans : List TopicPlan) : State :=
  { s with
    mesh := plans.map (fun pl =>
      (pl.topic, pl.kept.filter (fun q => decide (0 ≤ scoreOf p s q)))),
    peers := s.peers.map (fun e =>
      (e.1, if scoreOf p s e.1 < 0 then
        { e.2 with
          score := s.topics.foldl (fun sc t => Score.prune p.score sc s.now t) e.2.score }
      else e.2)) }

/-- The gossip actions: each topic of the mesh and the fanout sends its
gossip ids to the peers of the order at or above the gossip threshold,
up to `dLazy` targets, skipping the peers that already sit in that
topic's mesh or fanout. The ids come from the cache as it stands, so a
heartbeat emits gossip before it shifts the cache. -/
def gossipActions (p : Params) (s : State) (order : List Peer) : List Action :=
  let eligible :=
    order.filter (fun q => decide (p.thresholds.gossipThreshold ≤ scoreOf p s q))
  let topics := s.mesh.map Prod.fst ++ s.fanout.map Prod.fst
  topics.flatMap fun t =>
    let ids := Cache.MessageCache.gossipIds s.mcache t
    if ids = [] then []
    else
      let targets :=
        (eligible.filter (fun q =>
          !(memB q (meshOf s t)) && !(memB q (fanoutOf s t)))).take p.mesh.dLazy
      targets.map fun q => Action.sendRpc q (ihaveRpc t ids)

/-- The state at the start of the heartbeat: the decayed scores, the new
clock, the cleared backoff table, the pruned seen cache, and the shifted
message cache. -/
def freshState (p : Params) (s : State) (now : Millis) : State :=
  { s with
    peers := s.peers.map (fun e => (e.1, { e.2 with score := Score.decay p.score e.2.score })),
    now := now,
    lastHeartbeat := now,
    backoff := Cache.Backoff.clear s.backoff now,
    seen := Cache.SeenCache.prune s.seen now,
    mcache := Cache.MessageCache.shift s.mcache }

/-- The per-topic plans of the heartbeat. -/
def heartbeatPlans (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List TopicPlan :=
  planList p (freshState p s now) now order

/-- The state after the plan score updates. -/
def planScored (p : Params) (s : State) (now : Millis) (order : List Peer) : State :=
  applyPlanScores p (freshState p s now) (heartbeatPlans p s now order)

/-- The state after the heartbeat. -/
def heartbeatNext (p : Params) (s : State) (now : Millis) (order : List Peer) : State :=
  settleMesh p (planScored p s now order) (heartbeatPlans p s now order)

/-- The plan actions of the heartbeat. -/
def planActionsOf (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List Action :=
  (heartbeatPlans p s now order).flatMap (planActions p)

/-- The negative prune actions of the heartbeat. -/
def negativeActions (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List Action :=
  (heartbeatPlans p s now order).flatMap (fun pl =>
    (pl.kept.filter (fun q => decide (scoreOf p (planScored p s now order) q < 0))).map
      (fun q => Action.sendRpc q (pruneRpc pl.topic p.pruneBackoff)))

/-- The state the gossip reads: the mesh and the scores after the
heartbeat, and the message cache before the shift. The spec emits the
ids, then shifts the cache. -/
def gossipState (p : Params) (s : State) (now : Millis) (order : List Peer) : State :=
  { heartbeatNext p s now order with mcache := s.mcache }

/-- The actions of the heartbeat. Gossip is emitted after the mesh is
settled and before the cache shifts. -/
def heartbeatActions (p : Params) (s : State) (now : Millis) (order : List Peer) :
    List Action :=
  planActionsOf p s now order ++ negativeActions p s now order ++
    gossipActions p (gossipState p s now order) order

/-- The heartbeat: decay, the fresh clock and tables, the per-topic plan,
the score updates, the mesh write with the negative prune, and the
actions of the plan, the negative prune, and the gossip. -/
def heartbeat (p : Params) (s : State) (now : Millis) (order : List Peer) :
    State × List Action :=
  (heartbeatNext p s now order, heartbeatActions p s now order)

/-! ## The event handlers -/

/-- A peer joins: record it, and send the hello RPC with our topics. A
known peer keeps its record. -/
def join (_p : Params) (s : State) (peer : Peer) (proto : PubsubProto) :
    State × List Action :=
  let s1 :=
    if (peerOf s peer).isSome then s
    else setPeer s peer { score := Score.PeerState.zero, proto := proto, subs := [] }
  (s1, [Action.sendRpc peer (helloRpc s.topics)])

/-- A peer leaves: drop it from the peers, the meshes, the fanout
records, and the promise table. -/
def leave (s : State) (peer : Peer) : State × List Action :=
  ({ s with
     peers := s.peers.filter (fun e => decide (e.1 ≠ peer)),
     mesh := s.mesh.map (fun e => (e.1, e.2.filter (fun q => decide (q ≠ peer)))),
     fanout := s.fanout.map (fun e =>
       (e.1, { e.2 with peers := e.2.peers.filter (fun q => decide (q ≠ peer)) })),
     iwant := s.iwant.filter (fun e => decide (e.peer ≠ peer)) },
   [])

/-- One subscription option against the announced list. -/
def applySubOpts (subs : List TopicId) (o : Rpc.SubOpts) : List TopicId :=
  let t : TopicId := ⟨o.topicid⟩
  if o.subscribe then (if memB t subs then subs else t :: subs)
  else subs.filter (fun u => decide (u ≠ t))

/-- Update the announced topics of the sender. -/
def handleSubs (s : State) (sender : Peer) (subs : List Rpc.SubOpts) : State :=
  match peerOf s sender with
  | some pd => setPeer s sender { pd with subs := subs.foldl applySubOpts pd.subs }
  | none => s

/-- Handle the published messages of an RPC: validate, accept, cache,
score, deliver, and forward. -/
def handlePubs (p : Params) (s : State) (sender : Peer) (ms : List Message) :
    State × List Action :=
  let valid := ms.filter (fun m => validationOk p m)
  let invalid := ms.filter (fun m => !(validationOk p m))
  let r := accept s.seen s.now p.msgId [] s.seen valid
  let s1 : State :=
    { s with
      seen := r.cache,
      mcache := r.accepted.foldl (fun c m => c.put (p.msgId m) m) s.mcache }
  let s2 := invalid.foldl (fun st m =>
    updateScoreOf st sender (fun sc => Score.invalidDelivery p.score sc m.topic)) s1
  let s3 := r.accepted.foldl (fun st m =>
    updateScoreOf st sender (fun sc =>
      let sc' := Score.firstDelivery p.score sc m.topic
      if memB sender (meshOf s m.topic) then Score.meshDelivery p.score sc' m.topic else sc')) s2
  (s3, r.accepted.map (fun m => Action.deliver m) ++
    forwardPubs s sender r.accepted)

/-- Whether the promise table holds the pair. -/
def promised (ps : Cache.PromiseTable) (q : Peer) (id : MessageId) : Bool :=
  ps.any (fun e => decide (e.peer = q ∧ e.id = id))

/-- Handle one IHAVE: request the ids that are unseen, uncached, and not
promised, and record the promise. -/
def handleIhave (p : Params) (s : State) (sender : Peer) (i : Rpc.ControlIHave) :
    State × List Action :=
  let wanted := i.messageIds.filter (fun id =>
    !(s.seen.contains id s.now) && (Cache.MessageCache.get s.mcache id).isNone &&
      !(promised s.iwant sender id))
  let s1 : State :=
    { s with
      iwant := wanted.foldl
        (fun ps id => ps.promise sender id (s.now + p.iwantDeadline)) s.iwant }
  (s1, if wanted = [] then [] else [Action.sendRpc sender (iwantRpc wanted)])

/-- Handle one IWANT: answer each id that the message cache holds under
the same id. -/
def handleIwant (p : Params) (s : State) (sender : Peer) (w : Rpc.ControlIWant) :
    State × List Action :=
  let answers := w.messageIds.filterMap (fun id =>
    match Cache.MessageCache.get s.mcache id with
    | some m => if p.msgId m = id then some m else none
    | none => none)
  (s, answers.map (fun m => Action.sendRpc sender (publishRpc m)))

/-- Handle one GRAFT. An unknown topic is ignored. A member is a no-op.
A peer in backoff, or a mesh at `dHigh`, gets a prune. Otherwise the
peer enters the mesh and takes the graft score update. -/
def handleGraft (p : Params) (s : State) (sender : Peer) (g : Rpc.ControlGraft) :
    State × List Action :=
  if memB (⟨g.topicId⟩ : TopicId) s.topics then
    if memB sender (meshOf s ⟨g.topicId⟩) then (s, [])
    else if Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true then
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)])
    else if p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length then
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)])
    else
      match peerOf s sender with
      | some pd =>
          (setPeer (setTopicMesh s ⟨g.topicId⟩ (sender :: meshOf s ⟨g.topicId⟩)) sender
            { pd with score := Score.graft pd.score s.now ⟨g.topicId⟩ }, [])
      | none => (s, [])
  else (s, [])

/-- The state after a prune records the backoff pair. -/
def pruneState (p : Params) (s : State) (sender : Peer) (q : Rpc.ControlPrune) : State :=
  { s with
    backoff := Cache.Backoff.add s.backoff sender ⟨q.topicId⟩
      (match q.backoff with
        | some sec => sec * 1000
        | none => p.pruneBackoff) s.now }

/-- Handle one PRUNE: record the backoff pair, and remove the sender
from the topic mesh with the prune score update. -/
def handlePrune (p : Params) (s : State) (sender : Peer) (q : Rpc.ControlPrune) :
    State × List Action :=
  if memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) then
    match peerOf (pruneState p s sender q) sender with
    | some pd =>
        (setPeer (setTopicMesh (pruneState p s sender q) ⟨q.topicId⟩
            ((meshOf (pruneState p s sender q) ⟨q.topicId⟩).filter
              (fun r => decide (r ≠ sender)))) sender
           { pd with
             score := Score.prune p.score pd.score (pruneState p s sender q).now ⟨q.topicId⟩ }, [])
    | none => (pruneState p s sender q, [])
  else (pruneState p s sender q, [])

/-- Run one handler over a list, threading the state and appending the
actions. -/
def mapHandlers {β : Type} (f : State → β → State × List Action) :
    List β → State → State × List Action
  | [], s => (s, [])
  | b :: bs, s =>
      let r := f s b
      let r' := mapHandlers f bs r.1
      (r'.1, r.2 ++ r'.2)

/-- The state after the ihave handlers. -/
def controlIhaves (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handleIhave p st sender b) c.ihave s).1

/-- The state after the iwant handlers. -/
def controlIwants (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handleIwant p st sender b) c.iwant (controlIhaves p s sender c)).1

/-- The state after the graft handlers. -/
def controlGrafts (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handleGraft p st sender b) c.graft (controlIwants p s sender c)).1

/-- The state after the prune handlers. -/
def controlPrunes (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    State :=
  (mapHandlers (fun st b => handlePrune p st sender b) c.prune (controlGrafts p s sender c)).1

/-- The actions of the control handlers: ihave, iwant, graft, then prune. -/
def controlActions (p : Params) (s : State) (sender : Peer) (c : Rpc.ControlMessage) :
    List Action :=
  (mapHandlers (fun st b => handleIhave p st sender b) c.ihave s).2 ++
    (mapHandlers (fun st b => handleIwant p st sender b) c.iwant
      (controlIhaves p s sender c)).2 ++
    (mapHandlers (fun st b => handleGraft p st sender b) c.graft
      (controlIwants p s sender c)).2 ++
    (mapHandlers (fun st b => handlePrune p st sender b) c.prune
      (controlGrafts p s sender c)).2

/-- Handle the control envelope: ihave, iwant, graft, then prune. -/
def handleControl (p : Params) (s : State) (sender : Peer) :
    Option Rpc.ControlMessage → State × List Action
  | none => (s, [])
  | some c => (controlPrunes p s sender c, controlActions p s sender c)

/-- Handle a decoded RPC: subscriptions, published messages, control. -/
def handleRpc (p : Params) (s : State) (sender : Peer) (rpc : Rpc.RPC) :
    State × List Action :=
  let s1 := handleSubs s sender rpc.subscriptions
  let (s2, a2) := handlePubs p s1 sender rpc.publish
  let (s3, a3) := handleControl p s2 sender rpc.control
  (s3, a2 ++ a3)

/-- The RPC branch gates: a graylisted peer is ignored, an unknown peer
is ignored, and a decode failure is the one error. -/
def rpcStep (p : Params) (s : State) (sender : Peer) (bytes : List Nat) :
    Except ProtocolError (State × List Action) :=
  if scoreOf p s sender < p.thresholds.graylistThreshold then .ok (s, [])
  else
    match peerOf s sender with
    | none => .ok (s, [])
    | some _ =>
        match decodeRpc bytes with
        | .error e => .error e
        | .ok rpc => .ok (handleRpc p s sender rpc)

/-- The fanout candidates: peers that announce the topic, at or above
score 0. -/
def fanoutCandidates (p : Params) (s : State) (topic : TopicId) : List Peer :=
  (announced s topic).filter (fun q => decide (0 ≤ scoreOf p s q))

/-- Extend the fanout of the topic to `d`, and set its last publish
time. -/
def extendFanout (p : Params) (s : State) (topic : TopicId) : State :=
  match lookupFanout s.fanout topic with
  | some f =>
      let need := if f.peers.length < p.mesh.d then p.mesh.d - f.peers.length else 0
      let cands := (fanoutCandidates p s topic).filter (fun q => !memB q f.peers)
      setTopicFanout s topic { peers := f.peers ++ cands.take need, lastPublished := s.now }
  | none =>
      setTopicFanout s topic
        { peers := (fanoutCandidates p s topic).take p.mesh.d, lastPublished := s.now }

/-- The forward targets of a publish: the mesh when we subscribe to the
topic, the fanout otherwise. -/
def publishTargets (_p : Params) (s : State) (topic : TopicId) : List Peer :=
  if memB topic s.topics then meshOf s topic else fanoutOf s topic

/-- The application publishes a message: validate, cache, record the id
as seen, extend the fanout when we do not subscribe, and forward to the
targets. The application already holds its own message, so this path
emits no deliver action. The seen record stops a later echo of the same
id from being forwarded again. -/
def publishLocal (p : Params) (s : State) (m : Message) : State × List Action :=
  if validationOk p m then
    let s1 : State :=
      { s with
        mcache := s.mcache.put (p.msgId m) m
        seen := s.seen.add (p.msgId m) s.now }
    let s2 := if memB m.topic s1.topics then s1 else extendFanout p s1 m.topic
    (s2, (publishTargets p s2 m.topic).map (fun q => Action.sendRpc q (publishRpc m)))
  else (s, [])

/-- The application subscribes: add the topic, move the fanout peers
into the mesh, fill to `d`, and graft the added peers. -/
def subscribe (p : Params) (s : State) (topic : TopicId) : State × List Action :=
  let s1 : State :=
    if memB topic s.topics then s else { s with topics := topic :: s.topics }
  let ps := meshOf s1 topic
  let ps1 := ps ++ (fanoutOf s1 topic).filter (fun q => !memB q ps)
  let need := if ps1.length < p.mesh.d then p.mesh.d - ps1.length else 0
  let cands := (announced s1 topic).filter (fun q =>
    !memB q ps1 && decide (0 ≤ scoreOf p s1 q) &&
      !(Cache.Backoff.active s1.backoff q topic s1.now))
  let added := cands.take need
  let s2 := setTopicMesh s1 topic ((ps1 ++ added).take p.mesh.dHigh)
  let s3 : State :=
    { s2 with fanout := s2.fanout.filter (fun e => decide (e.1 ≠ topic)) }
  (s3, added.map (fun q => Action.sendRpc q (graftRpc topic)))

/-- The application unsubscribes: drop the topic, empty its mesh and
fanout, prune the old mesh peers, and record the backoff pairs. -/
def unsubscribe (p : Params) (s : State) (topic : TopicId) : State × List Action :=
  let ps := meshOf s topic
  let s1 : State := { s with topics := s.topics.filter (fun t => decide (t ≠ topic)) }
  let s2 := setTopicMesh s1 topic []
  let s3 : State :=
    { s2 with fanout := s2.fanout.filter (fun e => decide (e.1 ≠ topic)) }
  let s4 := ps.foldl
    (fun st q => { st with backoff := Cache.Backoff.add st.backoff q topic p.pruneBackoff s.now })
    s3
  (s4, ps.map (fun q => Action.sendRpc q (pruneRpc topic p.pruneBackoff)))

/-! ## The transition and the driver -/

/-- One transition of the router. Every event is handled, and only an
RPC that does not decode returns an error. -/
def step (p : Params) (s : State) : Event → Except ProtocolError (State × List Action)
  | .peerJoined peer proto => .ok (join p s peer proto)
  | .peerLeft peer => .ok (leave s peer)
  | .rpc sender bytes => rpcStep p s sender bytes
  | .publish msg => .ok (publishLocal p s msg)
  | .subscribe topic => .ok (subscribe p s topic)
  | .unsubscribe topic => .ok (unsubscribe p s topic)
  | .tick now order =>
      if heartbeatDue p s now then .ok (heartbeat p s now order) else .ok (s, [])

/-- The transcript driver: the events in order. The first error stops
the run. -/
def run (p : Params) (s : State) : List Event → Except ProtocolError (State × List Action)
  | [] => .ok (s, [])
  | e :: es =>
      match step p s e with
      | .error err => .error err
      | .ok (s1, a1) =>
          match run p s1 es with
          | .error err => .error err
          | .ok (s2, a2) => .ok (s2, a1 ++ a2)

/-! ## The spec defaults -/

/-- The spec defaults: d 6, dLow 4, dHigh 12, dScore 4, dLazy 6,
heartbeat 1000 ms, fanout ttl 60000 ms, prune backoff 60000 ms, gossip
factor 25 percent, iwant deadline 3000 ms, window 5 over 3, seen
capacity 65536 and ttl 120000 ms, and zero score weights with no
configured topic. The numbers follow `gossipsub-v1.0.md` and the v1.1
recommendations. The seen capacity is a chosen memory bound that the
spec leaves open. `validationOk` uses `strictNoSign`, which requires
`from` and `seqno` to be absent, so the spec's default id `from ++ seqno`
would be empty for every accepted message. The default here is the
payload bytes. `Sign.defaultMsgId` stays available for a caller that
pairs it with `strictSign`. -/
def defaults : Params where
  score :=
    { topics := fun _ => none,
      global :=
        { appSpecificWeight := 0
          ipColocationFactorWeight := 0
          ipColocationFactorThreshold := 1
          behaviourPenaltyWeight := 0
          behaviourPenaltyThreshold := 0
          behaviourPenaltyDecay := scoreScale
          decayInterval := 1000
          decayToZero := 0
          topicScoreCap := 0 } }
  thresholds :=
    { gossipThreshold := 0
      publishThreshold := 0
      graylistThreshold := 0
      acceptPXThreshold := 0
      opportunisticGraftThreshold := 0 }
  mesh := { d := 6, dLow := 4, dHigh := 12, dScore := 4, dLazy := 6 }
  heartbeatInterval := 1000
  fanoutTtl := 60000
  pruneBackoff := 60000
  gossipFactor := 25
  iwantDeadline := 3000
  window := { historyLength := 5, historyGossip := 3, valid := by decide }
  seen := { capacity := 65536, ttl := 120000, valid := by decide }
  prims :=
    { unmarshalKey := fun _ => none
      inlineKey := fun _ => none
      idOfKey := fun _ => []
      verify := fun _ _ _ => false }
  msgId := fun m => ⟨m.data.getD []⟩

/-! ## Accessor lemmas -/

private theorem lookupTopic_upsertMesh_same (l : List (TopicId × List Peer)) (t : TopicId)
    (ps : List Peer) : lookupTopic (upsertMesh l t ps) t = ps := by
  induction l with
  | nil => simp [upsertMesh, lookupTopic]
  | cons e l ih =>
    obtain ⟨t', ps'⟩ := e
    by_cases h : t = t'
    · simp [upsertMesh, lookupTopic, h]
    · simp [upsertMesh, lookupTopic, h, ih]

private theorem lookupTopic_upsertMesh_ne (t' t : TopicId) (h : t' ≠ t)
    (l : List (TopicId × List Peer)) (ps : List Peer) :
    lookupTopic (upsertMesh l t ps) t' = lookupTopic l t' := by
  induction l with
  | nil => simp [upsertMesh, lookupTopic, h]
  | cons e l ih =>
    obtain ⟨u, us⟩ := e
    by_cases h2 : t = u
    · subst h2
      simp [upsertMesh, lookupTopic, h]
    · simp [upsertMesh, lookupTopic, h2, ih]

/-- The mesh of the written topic. -/
theorem meshOf_setTopicMesh_same (s : State) (t : TopicId) (ps : List Peer) :
    meshOf (setTopicMesh s t ps) t = ps := by
  simp [meshOf, setTopicMesh, lookupTopic_upsertMesh_same]

/-- A write of one topic leaves the mesh of another topic. -/
theorem meshOf_setTopicMesh_ne (s : State) (t t' : TopicId) (h : t' ≠ t)
    (ps : List Peer) : meshOf (setTopicMesh s t ps) t' = meshOf s t' := by
  simp [meshOf, setTopicMesh, lookupTopic_upsertMesh_ne t' t h]

private theorem lookupPeer_upsertPeer_same (l : List (Peer × PeerData)) (q : Peer)
    (pd : PeerData) : lookupPeer (upsertPeer l q pd) q = some pd := by
  induction l with
  | nil => simp [upsertPeer, lookupPeer]
  | cons e l ih =>
    obtain ⟨q', pd'⟩ := e
    by_cases h : q = q'
    · simp [upsertPeer, lookupPeer, h]
    · simp [upsertPeer, lookupPeer, h, ih]

private theorem lookupPeer_upsertPeer_ne (q' q : Peer) (h : q' ≠ q)
    (l : List (Peer × PeerData)) (pd : PeerData) :
    lookupPeer (upsertPeer l q pd) q' = lookupPeer l q' := by
  induction l with
  | nil => simp [upsertPeer, lookupPeer, h]
  | cons e l ih =>
    obtain ⟨u, ud⟩ := e
    by_cases h2 : q = u
    · subst h2
      simp [upsertPeer, lookupPeer, h]
    · simp [upsertPeer, lookupPeer, h2, ih]

/-- The record of the written peer. -/
theorem peerOf_setPeer_same (s : State) (q : Peer) (pd : PeerData) :
    peerOf (setPeer s q pd) q = some pd := by
  simp [peerOf, setPeer, lookupPeer_upsertPeer_same]

/-- A write of one peer leaves the record of another peer. -/
theorem peerOf_setPeer_ne (s : State) (q q' : Peer) (h : q' ≠ q) (pd : PeerData) :
    peerOf (setPeer s q pd) q' = peerOf s q' := by
  simp [peerOf, setPeer, lookupPeer_upsertPeer_ne q' q h]

private theorem lookupPeer_map (l : List (Peer × PeerData))
    (f : Peer → PeerData → PeerData) (q : Peer) :
    lookupPeer (l.map (fun e => (e.1, f e.1 e.2))) q = (lookupPeer l q).map (f q) := by
  induction l with
  | nil => simp [lookupPeer]
  | cons e l ih =>
    obtain ⟨q', pd'⟩ := e
    simp only [List.map_cons, lookupPeer]
    by_cases h : q = q'
    · subst h
      simp
    · simp [h, ih]

/-- The record of a peer after a map over the whole list. -/
theorem peerOf_mapPeers (s : State) (f : Peer → PeerData → PeerData) (q : Peer) :
    peerOf (mapPeers s f) q = (peerOf s q).map (f q) := by
  simp [peerOf, mapPeers, lookupPeer_map]

/-- The score of a peer after a map over the whole peer list. -/
theorem scoreOf_mapPeers (p : Params) (s : State) (f : Peer → PeerData → PeerData)
    (q : Peer) :
    scoreOf p (mapPeers s f) q =
      match peerOf s q with
      | some pd => Score.score p.score (f q pd).score s.now
      | none => 0 := by
  simp only [scoreOf, peerOf_mapPeers]
  cases h : peerOf s q <;> rfl

/-- The score reads only the peer list and the time. -/
theorem scoreOf_congr (p : Params) {s s' : State} (hpeers : s'.peers = s.peers)
    (hnow : s'.now = s.now) (q : Peer) : scoreOf p s' q = scoreOf p s q := by
  simp [scoreOf, peerOf, hpeers, hnow]

/-! ## Plan lemmas -/

/-- The plan of a topic keeps at most `dHigh` peers. -/
theorem planTopic_kept_le (p : Params) (s : State) (now : Millis) (order : List Peer)
    (t : TopicId) : (planTopic p s now order t).kept.length ≤ p.mesh.dHigh := by
  simp only [planTopic]
  rw [List.length_take]
  omega

/-- The lookup of a mesh rebuilt from a list of plans. -/
theorem lookupTopic_map_plans (plans : List TopicPlan) (f : TopicPlan → List Peer)
    (t : TopicId) :
    lookupTopic (plans.map (fun pl => (pl.topic, f pl))) t =
      match plans.find? (fun pl => decide (t = pl.topic)) with
      | some pl => f pl
      | none => [] := by
  induction plans with
  | nil => simp [lookupTopic]
  | cons pl rest ih =>
    simp only [List.map_cons]
    by_cases h : t = pl.topic
    · simp [lookupTopic, List.find?, h]
    · simp [lookupTopic, List.find?, h, ih]


/-- The mesh of a topic after the heartbeat mesh write. -/
theorem meshOf_settleMesh (p : Params) (s : State) (plans : List TopicPlan) (topic : TopicId) :
    meshOf (settleMesh p s plans) topic =
      match plans.find? (fun pl => decide (topic = pl.topic)) with
      | some pl => pl.kept.filter (fun q => decide (0 ≤ scoreOf p s q))
      | none => [] := by
  simp [meshOf, settleMesh, lookupTopic_map_plans]

/-! ## The mesh bound theorem -/

/-- After a heartbeat, every topic mesh holds at most `dHigh` peers.
The kept list is cut at `dHigh` by construction, and the negative prune
only removes peers. -/
theorem heartbeatMeshBound (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ topic, (meshOf s' topic).length ≤ p.mesh.dHigh := by
  intro topic
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  rw [heartbeatNext, meshOf_settleMesh]
  split
  · next pl hfind =>
    have hmem : pl ∈ heartbeatPlans p s now order := List.mem_of_find?_eq_some hfind
    have hmem' : pl ∈ (freshState p s now).mesh.map
        (fun e => planTopic p (freshState p s now) now order e.1) := by
      simpa [heartbeatPlans, planList] using hmem
    simp only [List.mem_map] at hmem'
    obtain ⟨e, _, rfl⟩ := hmem'
    exact Nat.le_trans (List.length_filter_le _ _)
      (planTopic_kept_le p (freshState p s now) now order e.1)
  · exact Nat.zero_le _


/-! ## The graylist gate theorem -/

/-- No RPC is processed from a peer below the graylist threshold. The
graylist premise is the only hypothesis, so the gate is what the
theorem proves: the step returns the pre-state and no actions, and it
does not consult the bytes. -/
theorem rpcGraylistIgnored (p : Params) (s : State) (sender : Peer)
    (bytes : List Nat)
    (hgray : scoreOf p s sender < p.thresholds.graylistThreshold) :
    step p s (.rpc sender bytes) = .ok (s, []) := by
  simp [step, rpcStep, hgray]


/-! ## The graft handler lemmas -/

private theorem handleGraft_unknown (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (h : memB (⟨g.topicId⟩ : TopicId) s.topics = false) :
    handleGraft p s sender g = (s, []) := by
  simp [handleGraft, h]

private theorem handleGraft_member (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = true) :
    handleGraft p s sender g = (s, []) := by
  simp [handleGraft, hsub, hm]

private theorem handleGraft_backoff (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true) :
    handleGraft p s sender g =
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)]) := by
  simp [handleGraft, hsub, hm, hb]

private theorem handleGraft_overfull (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false)
    (hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length) :
    handleGraft p s sender g =
      (s, [Action.sendRpc sender (pruneRpc ⟨g.topicId⟩ p.pruneBackoff)]) := by
  simp [handleGraft, hsub, hm, hb, hd]

private theorem handleGraft_add (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (pd : PeerData)
    (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false)
    (hd : ¬ p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length)
    (hpd : peerOf s sender = some pd) :
    handleGraft p s sender g =
      (setPeer (setTopicMesh s ⟨g.topicId⟩ (sender :: meshOf s ⟨g.topicId⟩)) sender
        { pd with score := Score.graft pd.score s.now ⟨g.topicId⟩ }, []) := by
  simp [handleGraft, hsub, hm, hb, hd, hpd]

private theorem handleGraft_add_none (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hm : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false)
    (hd : ¬ p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length)
    (hpd : peerOf s sender = none) :
    handleGraft p s sender g = (s, []) := by
  simp [handleGraft, hsub, hm, hb, hd, hpd]

private theorem meshOf_addPeer (s : State) (sender : Peer) (pd : PeerData) (t topic : TopicId)
    (h : topic ≠ t) :
    meshOf (setPeer (setTopicMesh s t (sender :: meshOf s t)) sender pd) topic
      = meshOf s topic := by
  simp [meshOf, setPeer, setTopicMesh, lookupTopic_upsertMesh_ne topic t h]

private theorem meshOf_addPeer_same (s : State) (sender : Peer) (pd : PeerData)
    (t : TopicId) :
    meshOf (setPeer (setTopicMesh s t (sender :: meshOf s t)) sender pd) t
      = sender :: meshOf s t := by
  simp [meshOf, setPeer, setTopicMesh, lookupTopic_upsertMesh_same]

private theorem handleGraft_mesh_other (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (topic : TopicId) (h : topic ≠ ⟨g.topicId⟩) :
    meshOf (handleGraft p s sender g).1 topic = meshOf s topic := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · rw [handleGraft_member p s sender g hsub hm]
    · have hm' : memB sender (meshOf s ⟨g.topicId⟩) = false := by
        cases h' : memB sender (meshOf s ⟨g.topicId⟩) <;> simp_all
      by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · rw [handleGraft_backoff p s sender g hsub hm' hb]
      · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
          cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
        by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · rw [handleGraft_overfull p s sender g hsub hm' hb' hd]
        · cases hpd : peerOf s sender with
          | none => rw [handleGraft_add_none p s sender g hsub hm' hb' hd hpd]
          | some pd =>
              rw [handleGraft_add p s sender g pd hsub hm' hb' hd hpd]
              exact meshOf_addPeer s sender _ ⟨g.topicId⟩ topic h
  · have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = false := by
      cases h' : memB (⟨g.topicId⟩ : TopicId) s.topics <;> simp_all
    rw [handleGraft_unknown p s sender g hsub']

private theorem handleGraft_mesh_same (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hnot : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length) :
    meshOf (handleGraft p s sender g).1 ⟨g.topicId⟩ = meshOf s ⟨g.topicId⟩ := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · rw [handleGraft_member p s sender g hsub hm]
    · by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · rw [handleGraft_backoff p s sender g hsub hnot hb]
      · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
          cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
        by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · rw [handleGraft_overfull p s sender g hsub hnot hb' hd]
        · exfalso
          omega
  · have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = false := by
      cases h' : memB (⟨g.topicId⟩ : TopicId) s.topics <;> simp_all
    rw [handleGraft_unknown p s sender g hsub']

private theorem handleGraft_prune (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (hsub0 : memB (⟨g.topicId⟩ : TopicId) s.topics = true)
    (hnot : memB sender (meshOf s ⟨g.topicId⟩) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length) :
    ∃ pr, Action.sendRpc sender pr ∈ (handleGraft p s sender g).2 ∧
      rpcPrunes pr ⟨g.topicId⟩ := by
  by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
  · exfalso
    rw [hnot] at hm
    simp at hm
  · by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
    · rw [handleGraft_backoff p s sender g hsub0 hnot hb]
      exact ⟨pruneRpc ⟨g.topicId⟩ p.pruneBackoff, by simp,
        by simp [pruneRpc, controlRpc, rpcPrunes]⟩
    · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
        cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
      rw [handleGraft_overfull p s sender g hsub0 hnot hb' hover]
      exact ⟨pruneRpc ⟨g.topicId⟩ p.pruneBackoff, by simp,
        by simp [pruneRpc, controlRpc, rpcPrunes]⟩

/-! ## The prune and control handler lemmas -/

private theorem filter_ne_self (l : List Peer) (sender : Peer) (h : memB sender l = false) :
    l.filter (fun r => decide (r ≠ sender)) = l := by
  rw [List.filter_eq_self]
  intro x hx
  have hx' : x ≠ sender := by
    intro hc
    subst hc
    have hmem : memB x l = true := memB_eq_true.mpr hx
    rw [h] at hmem
    simp at hmem
  simp [hx']

private theorem meshOf_pruneState (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (topic : TopicId) :
    meshOf (pruneState p s sender q) topic = meshOf s topic := by
  simp [pruneState, meshOf]

private theorem meshOf_setPeer (s : State) (q : Peer) (pd : PeerData) (topic : TopicId) :
    meshOf (setPeer s q pd) topic = meshOf s topic := by
  simp [meshOf, setPeer]

private theorem handlePrune_mesh_same (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (hnot : memB sender (meshOf s ⟨q.topicId⟩) = false) :
    meshOf (handlePrune p s sender q).1 ⟨q.topicId⟩ = meshOf s ⟨q.topicId⟩ := by
  have hst : meshOf (pruneState p s sender q) ⟨q.topicId⟩ = meshOf s ⟨q.topicId⟩ :=
    meshOf_pruneState p s sender q ⟨q.topicId⟩
  by_cases hm : memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) = true
  · cases hpd : peerOf (pruneState p s sender q) sender with
    | none =>
        simp only [handlePrune, hm, ite_true, hpd]
        exact hst
    | some pd =>
        have hf : (meshOf (pruneState p s sender q) ⟨q.topicId⟩).filter
            (fun r => decide (r ≠ sender))
              = meshOf (pruneState p s sender q) ⟨q.topicId⟩ := by
          apply filter_ne_self
          rw [hst]
          exact hnot
        simp only [handlePrune, hm, ite_true, hpd]
        rw [meshOf_setPeer, meshOf_setTopicMesh_same, hf, hst]
  · simp only [handlePrune, hm]
    exact hst

private theorem handlePrune_mesh_ne (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (topic : TopicId) (h : topic ≠ ⟨q.topicId⟩) :
    meshOf (handlePrune p s sender q).1 topic = meshOf s topic := by
  have hst : meshOf (pruneState p s sender q) topic = meshOf s topic :=
    meshOf_pruneState p s sender q topic
  by_cases hm : memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) = true
  · cases hpd : peerOf (pruneState p s sender q) sender with
    | none =>
        simp only [handlePrune, hm, ite_true, hpd]
        exact hst
    | some pd =>
        simp only [handlePrune, hm, ite_true, hpd]
        rw [meshOf_setPeer,
          meshOf_setTopicMesh_ne (pruneState p s sender q) ⟨q.topicId⟩ topic h, hst]
  · simp only [handlePrune, hm]
    exact hst

private theorem handlePrunes_mesh (p : Params) (s : State) (sender : Peer)
    (qs : List Rpc.ControlPrune) (topic : TopicId)
    (hnot : memB sender (meshOf s topic) = false) :
    meshOf (mapHandlers (fun st b => handlePrune p st sender b) qs s).1 topic
      = meshOf s topic := by
  induction qs generalizing s with
  | nil => simp [mapHandlers]
  | cons q qs ih =>
    simp only [mapHandlers]
    by_cases h : topic = ⟨q.topicId⟩
    · subst h
      rw [ih (s := (handlePrune p s sender q).1)
        (by rwa [handlePrune_mesh_same p s sender q hnot]),
        handlePrune_mesh_same p s sender q hnot]
    · rw [ih (s := (handlePrune p s sender q).1)
        (by rwa [handlePrune_mesh_ne p s sender q topic h]),
        handlePrune_mesh_ne p s sender q topic h]

private theorem handleIhave_mesh (p : Params) (s : State) (sender : Peer)
    (i : Rpc.ControlIHave) (topic : TopicId) :
    meshOf (handleIhave p s sender i).1 topic = meshOf s topic := by
  simp [handleIhave, meshOf]

private theorem handleIwant_mesh (p : Params) (s : State) (sender : Peer)
    (w : Rpc.ControlIWant) (topic : TopicId) :
    meshOf (handleIwant p s sender w).1 topic = meshOf s topic := by
  simp [handleIwant]

private theorem handleIhaves_mesh (p : Params) (s : State) (sender : Peer)
    (is : List Rpc.ControlIHave) (topic : TopicId) :
    meshOf (mapHandlers (fun st b => handleIhave p st sender b) is s).1 topic
      = meshOf s topic := by
  induction is generalizing s with
  | nil => simp [mapHandlers]
  | cons i is ih =>
    simp only [mapHandlers]
    rw [ih (s := (handleIhave p s sender i).1), handleIhave_mesh]

private theorem handleIwants_mesh (p : Params) (s : State) (sender : Peer)
    (ws : List Rpc.ControlIWant) (topic : TopicId) :
    meshOf (mapHandlers (fun st b => handleIwant p st sender b) ws s).1 topic
      = meshOf s topic := by
  induction ws generalizing s with
  | nil => simp [mapHandlers]
  | cons w ws ih =>
    simp only [mapHandlers]
    rw [ih (s := (handleIwant p s sender w).1), handleIwant_mesh]

private theorem topics_mapHandlers {β : Type} (f : State → β → State × List Action)
    (hf : ∀ (s : State) (b : β), (f s b).1.topics = s.topics) :
    ∀ (bs : List β) (s : State), (mapHandlers f bs s).1.topics = s.topics
  | [], s => rfl
  | b :: bs, s => by
      simp only [mapHandlers]
      rw [topics_mapHandlers f hf bs (f s b).1, hf s b]

private theorem handleIhave_topics (p : Params) (s : State) (sender : Peer)
    (i : Rpc.ControlIHave) : (handleIhave p s sender i).1.topics = s.topics := by
  simp [handleIhave]

private theorem handleIwant_topics (p : Params) (s : State) (sender : Peer)
    (w : Rpc.ControlIWant) : (handleIwant p s sender w).1.topics = s.topics := by
  simp [handleIwant]

private theorem handleGraft_topics (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) : (handleGraft p s sender g).1.topics = s.topics := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · simp [handleGraft, hsub, hm]
    · by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · simp [handleGraft, hsub, hm, hb]
      · by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · simp [handleGraft, hsub, hm, hb, hd]
        · cases hpd : peerOf s sender <;> simp [handleGraft, hsub, hm, hb, hd, hpd, setPeer, setTopicMesh]
  · simp [handleGraft, hsub]

private theorem pruneState_topics (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) : (pruneState p s sender q).topics = s.topics := by
  simp [pruneState]

private theorem handlePrune_topics (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) : (handlePrune p s sender q).1.topics = s.topics := by
  by_cases hm : memB sender (meshOf (pruneState p s sender q) ⟨q.topicId⟩) = true
  · cases hpd : peerOf (pruneState p s sender q) sender with
    | none =>
        simp only [handlePrune, hm, ite_true, hpd]
        exact pruneState_topics p s sender q
    | some pd =>
        simp only [handlePrune, hm, ite_true, hpd]
        simp [setPeer, setTopicMesh, pruneState]
  · simp only [handlePrune, hm]
    exact pruneState_topics p s sender q

private theorem controlIwants_topics (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) : (controlIwants p s sender c).topics = s.topics := by
  simp only [controlIwants, controlIhaves]
  rw [topics_mapHandlers (fun st b => handleIwant p st sender b)
      (fun st b => handleIwant_topics p st sender b),
    topics_mapHandlers (fun st b => handleIhave p st sender b)
      (fun st b => handleIhave_topics p st sender b)]

private theorem controlGrafts_topics (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) : (controlGrafts p s sender c).topics = s.topics := by
  simp only [controlGrafts]
  rw [topics_mapHandlers (fun st b => handleGraft p st sender b)
      (fun st b => handleGraft_topics p st sender b),
    controlIwants_topics]

private theorem handleGrafts_mesh (p : Params) (s : State) (sender : Peer)
    (gs : List Rpc.ControlGraft) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length) :
    meshOf (mapHandlers (fun st b => handleGraft p st sender b) gs s).1 topic
      = meshOf s topic := by
  induction gs generalizing s with
  | nil => simp [mapHandlers]
  | cons g gs ih =>
    simp only [mapHandlers]
    have htop : (handleGraft p s sender g).1.topics = s.topics :=
      handleGraft_topics p s sender g
    have hsub' : memB topic (handleGraft p s sender g).1.topics = true := by
      rw [htop]; exact hsub
    by_cases h : topic = ⟨g.topicId⟩
    · subst h
      have hm : meshOf (handleGraft p s sender g).1 ⟨g.topicId⟩ = meshOf s ⟨g.topicId⟩ :=
        handleGraft_mesh_same p s sender g hnot hover
      rw [ih (s := (handleGraft p s sender g).1) hsub' (by rw [hm]; exact hnot)
        (by rw [hm]; exact hover), hm]
    · have hm : meshOf (handleGraft p s sender g).1 topic = meshOf s topic :=
        handleGraft_mesh_other p s sender g topic h
      rw [ih (s := (handleGraft p s sender g).1) hsub' (by rw [hm]; exact hnot)
        (by rw [hm]; exact hover), hm]

private theorem handleGrafts_prune (p : Params) (s : State) (sender : Peer)
    (gs : List Rpc.ControlGraft) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length)
    (hg : ∃ g ∈ gs, g.topicId = topic.name) :
    ∃ pr, Action.sendRpc sender pr ∈
        (mapHandlers (fun st b => handleGraft p st sender b) gs s).2 ∧
      rpcPrunes pr topic := by
  induction gs generalizing s with
  | nil => simp at hg
  | cons g gs ih =>
    simp only [mapHandlers]
    by_cases hsame : g.topicId = topic.name
    · have ht : (⟨g.topicId⟩ : TopicId) = topic := by rw [hsame]
      have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = true := by
        rw [ht]; exact hsub
      have hnot' : memB sender (meshOf s ⟨g.topicId⟩) = false := by
        rw [ht]; exact hnot
      have hover' : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length := by
        rw [ht]; exact hover
      obtain ⟨pr, hpr, hrpc⟩ := handleGraft_prune p s sender g hsub' hnot' hover'
      refine ⟨pr, List.mem_append_left _ hpr, ?_⟩
      rwa [ht] at hrpc
    · have hg' : ∃ g' ∈ gs, g'.topicId = topic.name := by
        obtain ⟨g', hg'mem, hg'eq⟩ := hg
        rcases List.mem_cons.mp hg'mem with h | h
        · rw [h] at hg'eq
          exact absurd hg'eq hsame
        · exact ⟨g', h, hg'eq⟩
      have htop : (handleGraft p s sender g).1.topics = s.topics :=
        handleGraft_topics p s sender g
      have hmesh : meshOf (handleGraft p s sender g).1 topic = meshOf s topic := by
        by_cases h : topic = ⟨g.topicId⟩
        · subst h
          exact handleGraft_mesh_same p s sender g hnot hover
        · exact handleGraft_mesh_other p s sender g topic h
      obtain ⟨pr, hpr, hrpc⟩ := ih (s := (handleGraft p s sender g).1)
        (by rw [htop]; exact hsub) (by rw [hmesh]; exact hnot)
        (by rw [hmesh]; exact hover) hg'
      exact ⟨pr, List.mem_append_right _ hpr, hrpc⟩

private theorem handleControl_mesh (p : Params) (s : State) (sender : Peer)
    (c : Option Rpc.ControlMessage) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length) :
    meshOf (handleControl p s sender c).1 topic = meshOf s topic := by
  cases c with
  | none => rfl
  | some c =>
    have h1 : meshOf (controlIhaves p s sender c) topic = meshOf s topic := by
      simp only [controlIhaves]
      exact handleIhaves_mesh p s sender c.ihave topic
    have h2 : meshOf (controlIwants p s sender c) topic = meshOf s topic := by
      simp only [controlIwants]
      rw [handleIwants_mesh, h1]
    have h3 : meshOf (controlGrafts p s sender c) topic = meshOf s topic := by
      simp only [controlGrafts]
      rw [handleGrafts_mesh p (controlIwants p s sender c) sender c.graft topic
        (by rw [controlIwants_topics]; exact hsub)
        (by rw [h2]; exact hnot) (by rw [h2]; exact hover), h2]
    have h4 : meshOf (controlPrunes p s sender c) topic = meshOf s topic := by
      simp only [controlPrunes]
      rw [handlePrunes_mesh p (controlGrafts p s sender c) sender c.prune topic
        (by rw [h3]; exact hnot), h3]
    simp only [handleControl]
    exact h4

private theorem handleControl_prune (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) (topic : TopicId)
    (hsub : memB topic s.topics = true)
    (hnot : memB sender (meshOf s topic) = false)
    (hover : p.mesh.dHigh ≤ (meshOf s topic).length)
    (hg : ∃ g ∈ c.graft, g.topicId = topic.name) :
    ∃ pr, Action.sendRpc sender pr ∈ controlActions p s sender c ∧ rpcPrunes pr topic := by
  have h2 : meshOf (controlIwants p s sender c) topic = meshOf s topic := by
    simp only [controlIwants, controlIhaves]
    rw [handleIwants_mesh, handleIhaves_mesh]
  have htop : (controlIwants p s sender c).topics = s.topics :=
    controlIwants_topics p s sender c
  obtain ⟨pr, hpr, hrpc⟩ :=
    handleGrafts_prune p (controlIwants p s sender c) sender c.graft topic
      (by rw [htop]; exact hsub) (by rw [h2]; exact hnot) (by rw [h2]; exact hover) hg
  refine ⟨pr, ?_, hrpc⟩
  simp only [controlActions]
  exact List.mem_append_left _ (List.mem_append_right _ hpr)

/-! ## The RPC pipeline lemmas -/

private theorem updateScoreOf_mesh (s : State) (q : Peer)
    (f : Score.PeerState → Score.PeerState) (topic : TopicId) :
    meshOf (updateScoreOf s q f) topic = meshOf s topic := by
  simp [updateScoreOf, mapPeers, meshOf]

private theorem updateScoreOf_topics (s : State) (q : Peer)
    (f : Score.PeerState → Score.PeerState) :
    (updateScoreOf s q f).topics = s.topics := by
  simp [updateScoreOf, mapPeers]

private theorem foldl_updateScoreOf_mesh (ms : List Message) (s : State) (sender : Peer)
    (f : Message → Score.PeerState → Score.PeerState) (topic : TopicId) :
    meshOf (ms.foldl (fun st m => updateScoreOf st sender (f m)) s) topic
      = meshOf s topic := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    rw [List.foldl_cons, ih, updateScoreOf_mesh]

private theorem foldl_updateScoreOf_topics (ms : List Message) (s : State) (sender : Peer)
    (f : Message → Score.PeerState → Score.PeerState) :
    (ms.foldl (fun st m => updateScoreOf st sender (f m)) s).topics = s.topics := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih =>
    rw [List.foldl_cons, ih, updateScoreOf_topics]

private theorem handleSubs_mesh (s : State) (sender : Peer) (subs : List Rpc.SubOpts)
    (topic : TopicId) : meshOf (handleSubs s sender subs) topic = meshOf s topic := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer, meshOf]

private theorem handleSubs_topics (s : State) (sender : Peer) (subs : List Rpc.SubOpts) :
    (handleSubs s sender subs).topics = s.topics := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer]

private theorem handlePubs_mesh (p : Params) (s : State) (sender : Peer)
    (ms : List Message) (topic : TopicId) :
    meshOf (handlePubs p s sender ms).1 topic = meshOf s topic := by
  simp only [handlePubs]
  rw [foldl_updateScoreOf_mesh, foldl_updateScoreOf_mesh]
  simp [meshOf]

private theorem handlePubs_topics (p : Params) (s : State) (sender : Peer)
    (ms : List Message) : (handlePubs p s sender ms).1.topics = s.topics := by
  simp only [handlePubs]
  rw [foldl_updateScoreOf_topics, foldl_updateScoreOf_topics]

/-- The record of a peer after the heartbeat mesh write. -/
theorem peerOf_settleMesh (p : Params) (s : State) (plans : List TopicPlan) (q : Peer) :
    peerOf (settleMesh p s plans) q =
      (peerOf s q).map (fun pd =>
        if scoreOf p s q < 0 then
          { pd with score := s.topics.foldl (fun sc t => Score.prune p.score sc s.now t) pd.score }
        else pd) := by
  simp only [peerOf, settleMesh]
  induction s.peers with
  | nil => simp [lookupPeer]
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.map_cons, lookupPeer]
    by_cases h : q = a
    · subst h
      simp
    · simp [h, ih]

/-- The score of a peer after the heartbeat mesh write. -/
theorem scoreOf_settleMesh (p : Params) (s : State) (plans : List TopicPlan) (q : Peer) :
    scoreOf p (settleMesh p s plans) q =
      match peerOf s q with
      | some pd =>
          Score.score p.score
            (if scoreOf p s q < 0 then
              s.topics.foldl (fun sc t => Score.prune p.score sc s.now t) pd.score
            else pd.score) s.now
      | none => 0 := by
  unfold scoreOf
  rw [peerOf_settleMesh]
  cases h : peerOf s q with
  | none => simp
  | some pd =>
    by_cases hlt : Score.score p.score pd.score s.now < 0 <;>
      simp [scoreOf, settleMesh, h, hlt]

/-- The mesh of a topic after a heartbeat. -/
theorem meshOf_heartbeatNext (p : Params) (s : State) (now : Millis)
    (order : List Peer) (topic : TopicId) :
    meshOf (heartbeatNext p s now order) topic =
      match (heartbeatPlans p s now order).find? (fun pl => decide (topic = pl.topic)) with
      | some pl =>
          pl.kept.filter (fun q => decide (0 ≤ scoreOf p (planScored p s now order) q))
      | none => [] := by
  simp [heartbeatNext, settleMesh, meshOf, lookupTopic_map_plans]

/-! ## The score gate theorems -/

private theorem rpcHasIhave_pruneRpc (t : TopicId) (b : Millis) :
    ¬ rpcHasIhave (pruneRpc t b) := by
  simp [rpcHasIhave, pruneRpc, controlRpc]

private theorem rpcHasIhave_graftRpc (t : TopicId) : ¬ rpcHasIhave (graftRpc t) := by
  simp [rpcHasIhave, graftRpc, controlRpc]

/-- A gossip action targets a peer of the order at or above the gossip
threshold. -/
theorem mem_gossipActions (p : Params) (s : State) (order : List Peer)
    (to : Peer) (rpc : Rpc.RPC)
    (h : Action.sendRpc to rpc ∈ gossipActions p s order) :
    p.thresholds.gossipThreshold ≤ scoreOf p s to := by
  simp only [gossipActions, List.mem_flatMap] at h
  obtain ⟨t, _, ht⟩ := h
  split at ht
  · simp at ht
  · next ids hne =>
    simp only [List.mem_map] at ht
    obtain ⟨q, hq, hqr⟩ := ht
    cases hqr
    have htake := List.mem_of_mem_take hq
    rw [List.mem_filter] at htake
    obtain ⟨hbase, _⟩ := htake
    rw [List.mem_filter] at hbase
    obtain ⟨_, hscore⟩ := hbase
    exact of_decide_eq_true hscore

/-- The gossip state keeps the settled scores and replaces the cache, so
the score of a peer is the score after the heartbeat. -/
theorem scoreOf_gossipState (p : Params) (s : State) (now : Millis) (order : List Peer)
    (q : Peer) :
    scoreOf p (gossipState p s now order) q = scoreOf p (heartbeatNext p s now order) q := by
  simp [scoreOf, gossipState, peerOf, heartbeatNext]
theorem tickPruneNegative (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ topic peer, peer ∈ meshOf s' topic → 0 ≤ scoreOf p s' peer := by
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  intro topic peer hmem
  rw [meshOf_heartbeatNext] at hmem
  split at hmem
  · next pl hfind =>
    simp only [List.mem_filter] at hmem
    have hge : 0 ≤ scoreOf p (planScored p s now order) peer := of_decide_eq_true hmem.2
    have hscore : scoreOf p (heartbeatNext p s now order) peer
        = scoreOf p (planScored p s now order) peer := by
      simp only [heartbeatNext]
      rw [scoreOf_settleMesh]
      cases hpd : peerOf (planScored p s now order) peer with
      | none => simp [scoreOf, hpd]
      | some pd =>
        have hge' : 0 ≤ Score.score p.score pd.score (planScored p s now order).now := by
          simpa [scoreOf, hpd] using hge
        have hlt : ¬ Score.score p.score pd.score (planScored p s now order).now < 0 :=
          Int.not_lt_of_ge hge'
        simp [scoreOf, hpd, hlt]
    rw [hscore]
    exact hge
  · simp at hmem

/-- Every gossip action targets a peer at or above the gossip threshold
in the state after the heartbeat. The prune and graft actions fail the
ihave test. -/
theorem tickGossipGated (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ to rpc, Action.sendRpc to rpc ∈ acts → rpcHasIhave rpc →
      p.thresholds.gossipThreshold ≤ scoreOf p s' to := by
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  intro to rpc hmem hih
  simp only [heartbeatActions, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rcases hmem with hmem | hmem
    · simp only [planActionsOf, List.mem_flatMap] at hmem
      obtain ⟨pl, _, hpl⟩ := hmem
      simp only [planActions, List.mem_append, List.mem_map] at hpl
      rcases hpl with ⟨q, _, hq⟩ | ⟨q, _, hq⟩
      · cases hq
        exact absurd hih (rpcHasIhave_pruneRpc _ _)
      · cases hq
        exact absurd hih (rpcHasIhave_graftRpc _)
    · simp only [negativeActions, List.mem_flatMap, List.mem_map] at hmem
      obtain ⟨pl, _, q, _, hq⟩ := hmem
      cases hq
      exact absurd hih (rpcHasIhave_pruneRpc _ _)
  · rw [← scoreOf_gossipState]
    exact mem_gossipActions p (gossipState p s now order) order to rpc hmem

/-! ## The deduplication theorem -/

/-- Every accepted message was absent from the pre-state seen cache. -/
theorem accept_gate (c0 : Cache.SeenCache) (now : Millis) (idf : Sign.MsgIdFn)
    (done : List MessageId) (c : Cache.SeenCache) (ms : List Message) :
    ∀ m ∈ (accept c0 now idf done c ms).accepted, c0.contains (idf m) now = false := by
  induction ms generalizing done c with
  | nil => simp [accept]
  | cons m ms ih =>
    simp only [accept]
    split
    · exact ih done c
    · next hskip =>
      intro m' hm'
      rw [List.mem_cons] at hm'
      rcases hm' with hhead | hm'
      · rw [hhead]
        cases hc : c0.contains (idf m) now with
        | false => rfl
        | true => exact absurd (by rw [hc]; rfl) hskip
      · exact ih (idf m :: done) (c.add (idf m) now) m' hm'

private theorem forwardPubs_not_deliver (s : State) (sender : Peer) (ms : List Message)
    (m : Message) : Action.deliver m ∉ forwardPubs s sender ms := by
  intro h
  simp only [forwardPubs, List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, q, _, hq⟩ := h
  cases hq

/-- An inbound forward never goes back to the sender. -/
theorem forwardPubs_excludes_sender (s : State) (sender : Peer) (ms : List Message)
    (rpc : Rpc.RPC) : Action.sendRpc sender rpc ∉ forwardPubs s sender ms := by
  intro h
  simp only [forwardPubs, List.mem_flatMap, List.mem_map] at h
  rcases h with ⟨_, _, _, hqmem, heq⟩
  injection heq with hpeer _
  simp only [inboundTargets, List.mem_filter] at hqmem
  have hne : _ ≠ sender := of_decide_eq_true hqmem.2
  exact hne hpeer

private theorem handleIhave_not_deliver (p : Params) (s : State) (sender : Peer)
    (i : Rpc.ControlIHave) (m : Message) :
    Action.deliver m ∉ (handleIhave p s sender i).2 := by
  simp only [handleIhave]
  split <;> simp

private theorem handleIwant_not_deliver (p : Params) (s : State) (sender : Peer)
    (w : Rpc.ControlIWant) (m : Message) :
    Action.deliver m ∉ (handleIwant p s sender w).2 := by
  simp only [handleIwant]
  simp [List.mem_map]

private theorem handlePrune_not_deliver (p : Params) (s : State) (sender : Peer)
    (q : Rpc.ControlPrune) (m : Message) :
    Action.deliver m ∉ (handlePrune p s sender q).2 := by
  simp only [handlePrune]
  split
  · split <;> simp
  · simp

private theorem handleGraft_not_deliver (p : Params) (s : State) (sender : Peer)
    (g : Rpc.ControlGraft) (m : Message) :
    Action.deliver m ∉ (handleGraft p s sender g).2 := by
  by_cases hsub : memB (⟨g.topicId⟩ : TopicId) s.topics = true
  · by_cases hm : memB sender (meshOf s ⟨g.topicId⟩) = true
    · rw [handleGraft_member p s sender g hsub hm]
      simp
    · have hm' : memB sender (meshOf s ⟨g.topicId⟩) = false := by
        cases h' : memB sender (meshOf s ⟨g.topicId⟩) <;> simp_all
      by_cases hb : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = true
      · rw [handleGraft_backoff p s sender g hsub hm' hb]
        simp
      · have hb' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now = false := by
          cases h' : Cache.Backoff.active s.backoff sender ⟨g.topicId⟩ s.now <;> simp_all
        by_cases hd : p.mesh.dHigh ≤ (meshOf s ⟨g.topicId⟩).length
        · rw [handleGraft_overfull p s sender g hsub hm' hb' hd]
          simp
        · cases hpd : peerOf s sender with
          | none =>
              rw [handleGraft_add_none p s sender g hsub hm' hb' hd hpd]
              simp
          | some pd =>
              rw [handleGraft_add p s sender g pd hsub hm' hb' hd hpd]
              simp
  · have hsub' : memB (⟨g.topicId⟩ : TopicId) s.topics = false := by
      cases h' : memB (⟨g.topicId⟩ : TopicId) s.topics <;> simp_all
    rw [handleGraft_unknown p s sender g hsub']
    simp

private theorem mapHandlers_not_deliver {β : Type} (f : State → β → State × List Action)
    (hf : ∀ (s : State) (b : β) (m : Message), Action.deliver m ∉ (f s b).2) :
    ∀ (bs : List β) (s : State) (m : Message), Action.deliver m ∉ (mapHandlers f bs s).2 := by
  intro bs
  induction bs with
  | nil =>
      intro s m
      simp [mapHandlers]
  | cons b bs ih =>
      intro s m
      simp only [mapHandlers, List.mem_append, not_or]
      exact ⟨hf s b m, ih (f s b).1 m⟩

private theorem controlActions_not_deliver (p : Params) (s : State) (sender : Peer)
    (c : Rpc.ControlMessage) (m : Message) :
    Action.deliver m ∉ controlActions p s sender c := by
  intro h
  simp only [controlActions, List.mem_append] at h
  rcases h with h | h
  · rcases h with h | h
    · rcases h with h | h
      · exact mapHandlers_not_deliver _ (fun s b => handleIhave_not_deliver p s sender b) _ _ _ h
      · exact mapHandlers_not_deliver _ (fun s b => handleIwant_not_deliver p s sender b) _ _ _ h
    · exact mapHandlers_not_deliver _ (fun s b => handleGraft_not_deliver p s sender b) _ _ _ h
  · exact mapHandlers_not_deliver _ (fun s b => handlePrune_not_deliver p s sender b) _ _ _ h

/-- A message reaches the application only when the pre-state seen cache
does not hold its id. -/
private theorem handleSubs_seen (s : State) (sender : Peer) (subs : List Rpc.SubOpts) :
    (handleSubs s sender subs).seen = s.seen := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer]

private theorem handleSubs_now (s : State) (sender : Peer) (subs : List Rpc.SubOpts) :
    (handleSubs s sender subs).now = s.now := by
  cases h : peerOf s sender <;> simp [handleSubs, h, setPeer]

private theorem join_not_deliver (p : Params) (s : State) (peer : Peer)
    (proto : PubsubProto) (m : Message) : Action.deliver m ∉ (join p s peer proto).2 := by
  simp [join]

private theorem leave_not_deliver (s : State) (peer : Peer) (m : Message) :
    Action.deliver m ∉ (leave s peer).2 := by
  simp [leave]

private theorem publishLocal_not_deliver (p : Params) (s : State) (msg : Message)
    (m : Message) : Action.deliver m ∉ (publishLocal p s msg).2 := by
  unfold publishLocal
  by_cases h : validationOk p msg
  · simp [h, List.mem_map]
  · simp [h]

private theorem subscribe_not_deliver (p : Params) (s : State) (topic : TopicId)
    (m : Message) : Action.deliver m ∉ (subscribe p s topic).2 := by
  simp only [subscribe]
  intro h
  rw [List.mem_map] at h
  obtain ⟨q, -, hq⟩ := h
  cases hq

private theorem unsubscribe_not_deliver (p : Params) (s : State) (topic : TopicId)
    (m : Message) : Action.deliver m ∉ (unsubscribe p s topic).2 := by
  simp only [unsubscribe]
  intro h
  rw [List.mem_map] at h
  obtain ⟨q, -, hq⟩ := h
  cases hq

private theorem planActions_not_deliver (p : Params) (pl : TopicPlan) (m : Message) :
    Action.deliver m ∉ planActions p pl := by
  simp [planActions, List.mem_map]

private theorem planActionsOf_not_deliver (p : Params) (s : State) (now : Millis)
    (order : List Peer) (m : Message) :
    Action.deliver m ∉ planActionsOf p s now order := by
  intro h
  simp only [planActionsOf, List.mem_flatMap] at h
  obtain ⟨pl, -, hp⟩ := h
  exact planActions_not_deliver p pl m hp

private theorem negativeActions_not_deliver (p : Params) (s : State) (now : Millis)
    (order : List Peer) (m : Message) :
    Action.deliver m ∉ negativeActions p s now order := by
  intro h
  simp only [negativeActions, List.mem_flatMap, List.mem_map] at h
  obtain ⟨pl, -, q, -, hq⟩ := h
  cases hq

private theorem gossipActions_not_deliver (p : Params) (s : State) (order : List Peer)
    (m : Message) : Action.deliver m ∉ gossipActions p s order := by
  intro h
  simp only [gossipActions, List.mem_flatMap] at h
  obtain ⟨t, -, ht⟩ := h
  split at ht
  · simp at ht
  · simp only [List.mem_map] at ht
    obtain ⟨q, -, hq⟩ := ht
    cases hq

private theorem heartbeatActions_not_deliver (p : Params) (s : State) (now : Millis)
    (order : List Peer) (m : Message) :
    Action.deliver m ∉ heartbeatActions p s now order := by
  intro h
  simp only [heartbeatActions, List.mem_append] at h
  rcases h with h | h
  · rcases h with h | h
    · exact planActionsOf_not_deliver p s now order m h
    · exact negativeActions_not_deliver p s now order m h
  · exact gossipActions_not_deliver p (gossipState p s now order) order m h

/-- A message reaches the application only when the pre-state seen cache
does not hold its id. -/
theorem stepDeliverUnseen (p : Params) (s s' : State) (acts : List Action)
    (e : Event) (m : Message)
    (hstep : step p s e = .ok (s', acts)) (hdel : Action.deliver m ∈ acts) :
    Cache.SeenCache.contains s.seen (p.msgId m) s.now = false := by
  cases e with
  | peerJoined peer proto =>
      have h1 : join p s peer proto = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (join p s peer proto).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (join_not_deliver p s peer proto m)
  | peerLeft peer =>
      have h1 : leave s peer = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (leave s peer).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (leave_not_deliver s peer m)
  | publish msg =>
      have h1 : publishLocal p s msg = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (publishLocal p s msg).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (publishLocal_not_deliver p s msg m)
  | subscribe topic =>
      have h1 : subscribe p s topic = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (subscribe p s topic).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (subscribe_not_deliver p s topic m)
  | unsubscribe topic =>
      have h1 : unsubscribe p s topic = (s', acts) := by
        simpa only [step, Except.ok.injEq] using hstep
      have hacts : acts = (unsubscribe p s topic).2 := by rw [h1]
      rw [hacts] at hdel
      exact absurd hdel (unsubscribe_not_deliver p s topic m)
  | tick now order =>
      by_cases hdue : heartbeatDue p s now
      · have h1 : heartbeat p s now order = (s', acts) := by
          simpa only [step, ite_eq_left hdue, Except.ok.injEq] using hstep
        have hacts : acts = (heartbeat p s now order).2 := by rw [h1]
        simp only [heartbeat] at hacts
        rw [hacts] at hdel
        exact absurd hdel (heartbeatActions_not_deliver p s now order m)
      · have h1 : (s, ([] : List Action)) = (s', acts) := by
          simpa only [step, ite_eq_right hdue, Except.ok.injEq] using hstep
        have hacts : acts = [] := by
          have hs := congrArg Prod.snd h1
          simpa using hs
        rw [hacts] at hdel
        simp at hdel
  | rpc sender bytes =>
      simp only [step, rpcStep] at hstep
      split at hstep
      · have h1 : (s, ([] : List Action)) = (s', acts) := by
          simpa only [Except.ok.injEq] using hstep
        have hacts : acts = [] := by
          have hs := congrArg Prod.snd h1
          simpa using hs
        rw [hacts] at hdel
        simp at hdel
      · split at hstep
        · have h1 : (s, ([] : List Action)) = (s', acts) := by
            simpa only [Except.ok.injEq] using hstep
          have hacts : acts = [] := by
            have hs := congrArg Prod.snd h1
            simpa using hs
          rw [hacts] at hdel
          simp at hdel
        · split at hstep
          · cases hstep
          · next rpc hdec =>
            have h1 : handleRpc p s sender rpc = (s', acts) := by
              simpa only [Except.ok.injEq] using hstep
            have hacts : acts = (handleRpc p s sender rpc).2 := by rw [h1]
            rw [hacts] at hdel
            simp only [handleRpc, List.mem_append] at hdel
            rcases hdel with hdel | hdel
            · simp only [handlePubs, List.mem_append] at hdel
              rcases hdel with hdl | hdl
              · simp only [List.mem_map] at hdl
                obtain ⟨m', hm', heq⟩ := hdl
                have hseen : (handleSubs s sender rpc.subscriptions).seen = s.seen :=
                  handleSubs_seen s sender rpc.subscriptions
                have hnow : (handleSubs s sender rpc.subscriptions).now = s.now :=
                  handleSubs_now s sender rpc.subscriptions
                cases heq
                have hgate := accept_gate (handleSubs s sender rpc.subscriptions).seen
                  (handleSubs s sender rpc.subscriptions).now p.msgId []
                  (handleSubs s sender rpc.subscriptions).seen
                  (List.filter (fun m => validationOk p m) rpc.publish) m hm'
                rwa [hseen, hnow] at hgate
              · exact absurd hdl
                  (forwardPubs_not_deliver (handleSubs s sender rpc.subscriptions) sender
                    ((accept (handleSubs s sender rpc.subscriptions).seen
                        (handleSubs s sender rpc.subscriptions).now p.msgId []
                        (handleSubs s sender rpc.subscriptions).seen
                        (List.filter (fun m => validationOk p m) rpc.publish)).accepted) m)
            · cases hctl : rpc.control with
              | none =>
                  rw [hctl] at hdel
                  simp [handleControl] at hdel
              | some c =>
                  rw [hctl] at hdel
                  simp only [handleControl] at hdel
                  exact absurd hdel (controlActions_not_deliver p _ sender c m)

/-! ## The backoff theorem -/

private theorem rpcGrafts_graftRpc (t t' : TopicId) (h : rpcGrafts (graftRpc t) t') : t' = t := by
  simp only [rpcGrafts, graftRpc, controlRpc, List.mem_cons, List.mem_nil_iff, or_false] at h
  obtain ⟨g, hg, hgt⟩ := h
  subst hg
  obtain ⟨tn⟩ := t
  obtain ⟨t'n⟩ := t'
  simpa using hgt.symm

private theorem rpcGrafts_pruneRpc (t t' : TopicId) (b : Millis) :
    ¬ rpcGrafts (pruneRpc t b) t' := by
  simp [rpcGrafts, pruneRpc, controlRpc]

private theorem rpcGrafts_ihaveRpc (t t' : TopicId) (ids : List MessageId) :
    ¬ rpcGrafts (ihaveRpc t ids) t' := by
  simp [rpcGrafts, ihaveRpc, controlRpc]

private theorem freshState_backoff (p : Params) (s : State) (now : Millis) :
    (freshState p s now).backoff = Cache.Backoff.clear s.backoff now := by
  simp [freshState]

private theorem planTopic_added_backoff (p : Params) (s : State) (now : Millis)
    (order : List Peer) (topic : TopicId) {q : Peer}
    (h : q ∈ (planTopic p s now order topic).added) :
    Cache.Backoff.active s.backoff q topic now = false := by
  simp only [planTopic] at h
  have hc : q ∈ order.filter (fun q =>
      !memB q (meshOf s topic) && !(Cache.Backoff.active s.backoff q topic now) &&
        (peerOf s q).isSome && decide (0 ≤ scoreOf p s q)) := List.mem_of_mem_take h
  cases hb : Cache.Backoff.active s.backoff q topic now with
  | false => rfl
  | true =>
      exfalso
      simp only [List.mem_filter] at hc
      rw [hb] at hc
      simp at hc

/-- The heartbeat never grafts a peer whose backoff is active. -/
theorem tickNoBackoffGraft (p : Params) (s s' : State) (acts : List Action)
    (now : Millis) (order : List Peer)
    (hdue : heartbeatDue p s now)
    (hstep : step p s (.tick now order) = .ok (s', acts)) :
    ∀ to rpc topic, Action.sendRpc to rpc ∈ acts → rpcGrafts rpc topic →
      Cache.Backoff.active s.backoff to topic now = false := by
  simp only [step, ite_eq_left hdue, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl⟩ := hstep
  intro to rpc topic hmem hgraft
  simp only [heartbeatActions, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · rcases hmem with hmem | hmem
    · simp only [planActionsOf, List.mem_flatMap] at hmem
      obtain ⟨pl, hpl, hmem⟩ := hmem
      simp only [planActions, List.mem_append, List.mem_map] at hmem
      rcases hmem with ⟨q, hq, hqeq⟩ | ⟨q, hq, hqeq⟩
      · cases hqeq
        exact absurd hgraft (rpcGrafts_pruneRpc _ _ _)
      · cases hqeq
        have htopic : topic = pl.topic := rpcGrafts_graftRpc pl.topic topic hgraft
        subst htopic
        have hpl' : pl ∈ (freshState p s now).mesh.map
            (fun e => planTopic p (freshState p s now) now order e.1) := by
          simpa [heartbeatPlans, planList] using hpl
        simp only [List.mem_map] at hpl'
        obtain ⟨e, -, rfl⟩ := hpl'
        have hb := planTopic_added_backoff p (freshState p s now) now order e.1 hq
        change Cache.Backoff.active s.backoff to e.1 now = false
        cases hcase : Cache.Backoff.active s.backoff to e.1 now with
        | false => rfl
        | true =>
            exfalso
            have hclear := Cache.clear_keeps_active s.backoff to e.1 now hcase
            rw [← freshState_backoff p s now] at hclear
            rw [hb] at hclear
            simp at hclear
    · simp only [negativeActions, List.mem_flatMap, List.mem_map] at hmem
      obtain ⟨pl, -, q, -, hqeq⟩ := hmem
      cases hqeq
      exact absurd hgraft (rpcGrafts_pruneRpc _ _ _)
  · simp only [gossipActions, List.mem_flatMap] at hmem
    obtain ⟨t, -, ht⟩ := hmem
    split at ht
    · simp at ht
    · simp only [List.mem_map] at ht
      obtain ⟨q, -, hqeq⟩ := ht
      cases hqeq
      exact absurd hgraft (rpcGrafts_ihaveRpc _ _ _)

end Libp2p.Protocols.Gossipsub.Core
