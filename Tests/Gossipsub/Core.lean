import Tests.Support
import Libp2p.Protocols.Gossipsub.Core

/-!
# Gossipsub suite: the router core

Transcript checks for the gossipsub v1.1 router: the mesh fill and
prune, the backoff, the score gates, the deduplication, the IWANT
answers, the fanout, and the rejection cases. The events, the times, and
the peer orders are fixed, so every run replays.

The spec sections are `vendor/specs/pubsub/gossipsub/gossipsub-v1.0.md`
(the router, the heartbeat, the mesh, the fanout) and
`gossipsub-v1.1.md` (the score gates, the backoff).
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Core

open Libp2p.Protocols
open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Core

/-! ## Fixtures -/

private def ta : TopicId := ⟨"t"⟩
private def tb : TopicId := ⟨"u"⟩

private def pa : Peer := ⟨[1], "a"⟩
private def pb : Peer := ⟨[2], "b"⟩
private def pc : Peer := ⟨[3], "c"⟩
private def pd : Peer := ⟨[4], "d"⟩
private def px : Peer := ⟨[9], "x"⟩

private def prims : Sign.Prims :=
  { unmarshalKey := fun _ => none
    inlineKey := fun _ => none
    idOfKey := fun _ => []
    verify := fun _ _ _ => false }

/-- The test parameters: a small mesh, and the message id is the data
bytes, so two messages of different payloads have different ids. -/
private def baseParams : Params :=
  { defaults with
    mesh := { d := 2, dLow := 1, dHigh := 3, dScore := 1, dLazy := 2 }
    prims := prims
    msgId := fun m => ⟨m.data.getD []⟩ }

/-- Every peer is below this graylist threshold. -/
private def grayParams : Params :=
  { baseParams with
    thresholds := { baseParams.thresholds with graylistThreshold := 1 } }

/-- No peer reaches this gossip threshold. -/
private def gossipParams : Params :=
  { baseParams with
    thresholds := { baseParams.thresholds with gossipThreshold := 1 } }

/-- The topic parameters of the scoring checks: one invalid delivery
costs a full score unit, and the decay keeps the counters. -/
private def scoreTopic : Score.TopicParams :=
  { topicWeight := 1
    timeInMeshWeight := 0
    timeInMeshQuantum := 1
    timeInMeshCap := 0
    firstMessageDeliveriesWeight := 0
    firstMessageDeliveriesDecay := scoreScale
    firstMessageDeliveriesCap := 0
    meshMessageDeliveriesWeight := 0
    meshMessageDeliveriesDecay := scoreScale
    meshMessageDeliveriesThreshold := 0
    meshMessageDeliveriesCap := 0
    meshMessageDeliveriesActivation := 0
    meshMessageDeliveriesWindow := 0
    meshFailurePenaltyWeight := 0
    meshFailurePenaltyDecay := scoreScale
    invalidMessageDeliveriesWeight := -1000
    invalidMessageDeliveriesDecay := scoreScale }

/-- The parameters with the topic `t` configured. -/
private def cfgParams : Params :=
  { baseParams with
    score := { baseParams.score with topics := fun t => if t = ta then some scoreTopic else none } }

private def peerRec (subs : List TopicId) : PeerData :=
  { score := Score.PeerState.zero, proto := .meshsub, subs := subs }

private def emptyState : State :=
  { peers := []
    mesh := []
    fanout := []
    mcache := Cache.MessageCache.empty baseParams.window
    seen := Cache.SeenCache.empty baseParams.seen
    backoff := []
    iwant := []
    topics := []
    now := 0
    lastHeartbeat := 0 }

/-- A state with the four peers known and the topic `t` subscribed. -/
private def known : State :=
  { emptyState with
    peers := [(pa, peerRec [ta]), (pb, peerRec [ta]), (pc, peerRec [ta]), (pd, peerRec [ta])]
    topics := [ta] }

/-- A message that passes `strictNoSign`: the four signed fields are
absent. The payload is the message id. -/
private def msgOf (topic : TopicId) (payload : List Nat) : Message :=
  { «from» := none, data := some payload, seqno := none, topic := topic,
    signature := none, key := none }

/-- A message with a `from` field, which fails `strictNoSign`. -/
private def badMsg : Message :=
  { «from» := some [9], data := some [1], seqno := none, topic := ta,
    signature := none, key := none }

private def rpcOfPublish (ms : List Message) : Rpc.RPC :=
  { subscriptions := [], publish := ms, control := none }

private def rpcOfControl (c : Rpc.ControlMessage) : Rpc.RPC :=
  { subscriptions := [], publish := [], control := some c }

private def controlOf (grafts : List Rpc.ControlGraft) (prunes : List Rpc.ControlPrune) : Rpc.ControlMessage :=
  { ihave := [], iwant := [], graft := grafts, prune := prunes }

private def pruneOf (topic : TopicId) : Rpc.ControlPrune :=
  { topicId := topic.name, peers := [], backoff := none }

private def graftOf (topic : TopicId) : Rpc.ControlGraft := { topicId := topic.name }

/-- Malformed bytes: field 1 of length 5 with one byte behind it. -/
private def malformed : List Nat := [10, 5, 1]

/-! ## Result accessors -/

private def stateOf : Except ProtocolError (State × List Action) → State
  | .ok (s, _) => s
  | .error _ => emptyState

private def actionsOf : Except ProtocolError (State × List Action) → List Action
  | .ok (_, a) => a
  | .error _ => []

private def isDecodeError : Except ProtocolError (State × List Action) → Bool
  | .error (.decode _) => true
  | _ => false

private def isOk : Except ProtocolError (State × List Action) → Bool
  | .ok _ => true
  | .error _ => false

private def delivers (m : Message) (l : List Action) : Nat :=
  (l.filter (fun a => match a with
    | .deliver m' => decide (m' = m)
    | .sendRpc _ _ => false)).length

private def sendsTo (q : Peer) (l : List Action) : Nat :=
  (l.filter (fun a => match a with
    | .sendRpc q' _ => decide (q' = q)
    | .deliver _ => false)).length

private def sends (l : List Action) (test : Rpc.RPC → Bool) : Nat :=
  (l.filter (fun a => match a with
    | .sendRpc _ r => test r
    | .deliver _ => false)).length

private def isPrune (t : TopicId) (r : Rpc.RPC) : Bool :=
  match r.control with
  | some c => c.prune.any (fun p => decide (p.topicId = t.name))
  | none => false

private def isGraft (t : TopicId) (r : Rpc.RPC) : Bool :=
  match r.control with
  | some c => c.graft.any (fun g => decide (g.topicId = t.name))
  | none => false

private def hasIhave (r : Rpc.RPC) : Bool :=
  match r.control with
  | some c => !c.ihave.isEmpty
  | none => false
private def hasPublish (r : Rpc.RPC) : Bool := !r.publish.isEmpty

private def pruneCount (t : TopicId) (l : List Action) : Nat := sends l (isPrune t)
private def graftCount (t : TopicId) (l : List Action) : Nat := sends l (isGraft t)
private def publishCount (l : List Action) : Nat := sends l hasPublish
private def ihaveCount (l : List Action) : Nat := sends l hasIhave

private def invalidCount (s : State) (q : Peer) (t : TopicId) : Nat :=
  match peerOf s q with
  | some pd => (Score.countersOf pd.score t).invalidMessageDeliveries
  | none => 0

/-- The counters of a peer with one invalid delivery. -/
private def negCounters : Score.TopicCounters :=
  { Score.TopicCounters.zero with
    inMesh := true, graftTime := 0, invalidMessageDeliveries := 1 }

/-- The score state of a peer with one invalid delivery in topic `t`. -/
private def negPeerState : Score.PeerState :=
  { Score.PeerState.zero with topics := [(ta, negCounters)] }

/-- A peer with one invalid delivery in a topic whose weight is -1000.
Its score is -1. -/
private def negPeerData : PeerData :=
  { score := negPeerState, proto := .meshsub, subs := [ta] }

/-- The state with the negative peer in the mesh of `t`. -/
private def negState : State :=
  { emptyState with
    peers := [(pa, negPeerData)]
    topics := [ta]
    mesh := [(ta, [pa])]
    now := 0
    lastHeartbeat := 0 }

private def meshIs (s : State) (t : TopicId) (ps : List Peer) : Bool := decide (meshOf s t = ps)

/-! ## Checks -/

/-- Run the checks of this module. -/
def run (r : Runner) : IO Unit := do
  r.section "gossipsub Core"
    "vendor/specs/pubsub/gossipsub/gossipsub-v1.0.md, gossipsub-v1.1.md"

  -- A malformed RPC is the one error constructor.
  r.check "core.reject.malformed-rpc"
    (isDecodeError (step baseParams known (.rpc pa malformed)))

  -- The graylist gate runs before the decode: malformed bytes from a
  -- graylisted peer are ignored, not rejected.
  r.check "core.reject.graylist-malformed-rpc-ignored"
    (match step grayParams known (.rpc pa malformed) with
     | .ok (s', acts) => acts = [] && meshIs s' ta (meshOf known ta)
     | _ => false)

  -- The graylist gate ignores a valid RPC too.
  r.check "core.reject.graylist-valid-rpc-ignored"
    (match step grayParams known (.rpc pa (Pb.encodeMessage (rpcOfControl (controlOf [graftOf ta] [])))) with
     | .ok (s', acts) => acts = [] && meshIs s' ta (meshOf known ta)
     | _ => false)

  -- An unknown peer is ignored.
  r.check "core.reject.unknown-peer-ignored"
    (match step baseParams known (.rpc px (Pb.encodeMessage (rpcOfControl (controlOf [graftOf ta] [])))) with
     | .ok (s', acts) => acts = [] && meshIs s' ta (meshOf known ta)
     | _ => false)

  -- A graft for a topic we do not serve draws no prune answer.
  r.check "core.reject.graft-unknown-topic-ignored"
    (match step baseParams known (.rpc pa (Pb.encodeMessage (rpcOfControl (controlOf [graftOf tb] [])))) with
     | .ok (s', acts) => acts = [] && meshIs s' tb []
     | _ => false)

  -- A graft inside an active backoff draws a prune and adds no peer.
  r.check "core.reject.graft-backoff-pruned"
    (match step baseParams
        { known with backoff := Cache.Backoff.add [] pa ta 60000 0, now := 1000 }
        (.rpc pa (Pb.encodeMessage (rpcOfControl (controlOf [graftOf ta] [])))) with
     | .ok (s', acts) => pruneCount ta acts = 1 && meshIs s' ta []
     | _ => false)

  -- A graft when the mesh holds `dHigh` peers draws a prune.
  r.check "core.reject.graft-at-dHigh-pruned"
    (match step baseParams { known with mesh := [(ta, [pb, pc, pd])] }
        (.rpc pa (Pb.encodeMessage (rpcOfControl (controlOf [graftOf ta] [])))) with
     | .ok (s', acts) => pruneCount ta acts = 1 && meshIs s' ta [pb, pc, pd]
     | _ => false)

  -- An IWANT for an id the message cache does not hold draws no answer.
  r.check "core.reject.iwant-uncached-no-answer"
    (match step baseParams known
        (.rpc pa (Pb.encodeMessage (iwantRpc [⟨[7]⟩]))) with
     | .ok (_, acts) => publishCount acts = 0
     | _ => false)

  -- A message that fails `strictNoSign` draws no deliver and no
  -- forward, and increments the invalid delivery counter.
  r.check "core.reject.invalid-signature-no-forward"
    (match step cfgParams { emptyState with peers := [(pa, peerRec [ta])], topics := [ta] }
        (.rpc pa (Pb.encodeMessage (rpcOfPublish [badMsg]))) with
     | .ok (s', acts) => delivers badMsg acts = 0 && publishCount acts = 0 &&
         invalidCount s' pa ta = 1
     | _ => false)

  -- A repeated id inside one event is delivered once.
  r.check "core.reject.duplicate-delivered-once"
    (match step baseParams known
        (.rpc pa (Pb.encodeMessage (rpcOfPublish [msgOf ta [1], msgOf ta [1]]))) with
     | .ok (_, acts) => delivers (msgOf ta [1]) acts = 1
     | _ => false)

  -- A tick before the interval ends does no maintenance.
  r.check "core.reject.early-tick-no-maintenance"
    (match step baseParams { known with lastHeartbeat := 0, now := 500 }
        (.tick 500 [pa, pb, pc, pd]) with
     | .ok (s', acts) => acts = [] && meshIs s' ta (meshOf known ta)
     | _ => false)

  -- A prune from a peer outside the mesh still records the backoff pair.
  r.check "core.reject.prune-from-nonmesh-records-backoff"
    (match step baseParams { known with now := 1000 }
        (.rpc pa (Pb.encodeMessage (rpcOfControl (controlOf [] [pruneOf ta])))) with
     | .ok (s', _) => Cache.Backoff.active s'.backoff pa ta s'.now
     | _ => false)

  -- The mesh fill of a subscribe: `d` peers, one graft each.
  r.check "core.mesh.fill"
    (let e := step baseParams known (.subscribe ta)
     let s := stateOf e
     let a := actionsOf e
     decide ((meshOf s ta).length = 2) && graftCount ta a = 2)

  -- An overfull mesh is pruned to `d` at the heartbeat.
  r.check "core.mesh.prune"
    (match step baseParams
        { known with mesh := [(ta, [pa, pb, pc, pd])], lastHeartbeat := 0, now := 0 }
        (.tick 1000 []) with
     | .ok (s', acts) => meshIs s' ta [pc, pd] && pruneCount ta acts = 2
     | _ => false)

  -- Gossip stays away from a peer below the gossip threshold.
  r.check "core.gossip.threshold"
    (match step gossipParams
        { known with mcache := (Cache.MessageCache.empty baseParams.window).put ⟨[1]⟩ (msgOf ta [1]) }
        (.tick 1000 [pa, pb, pc, pd]) with
     | .ok (_, acts) => ihaveCount acts = 0
     | _ => false)

  -- Gossip goes to peers outside the mesh, and the ids are the ones the
  -- cache held before the shift. `pa` and `pb` sit in the mesh, so a
  -- router that advertised to mesh members would reach them.
  r.check "core.gossip.outside-mesh"
    (match step baseParams
        { known with
          mesh := [(ta, [pa, pb])]
          mcache := (Cache.MessageCache.empty baseParams.window).put ⟨[1]⟩ (msgOf ta [1]) }
        (.tick 1000 [pa, pb, pc, pd]) with
     | .ok (_, acts) => sendsTo pa acts = 0 && sendsTo pb acts = 0 &&
         sendsTo pc acts = 1 && sendsTo pd acts = 1 && ihaveCount acts = 2
     | _ => false)

  -- A mesh peer below score 0 leaves the mesh at the heartbeat.
  r.check "core.score.negative-pruned"
    (match step cfgParams negState (.tick 1000 []) with
     | .ok (s', acts) => meshIs s' ta [] && pruneCount ta acts = 1
     | _ => false)

  -- A join sends the hello RPC; a leave drops the peer from the mesh.
  r.check "core.join.hello"
    (match step baseParams { known with peers := [] } (.peerJoined pa .meshsub) with
     | .ok (s', acts) => sendsTo pa acts = 1 && (peerOf s' pa).isSome
     | _ => false)
  r.check "core.leave.mesh"
    (match step baseParams { known with mesh := [(ta, [pa, pb])] } (.peerLeft pa) with
     | .ok (s', acts) => acts = [] && meshIs s' ta [pb]
     | _ => false)

  -- An inbound message reaches every other mesh peer, and not the sender.
  r.check "core.forward.mesh"
    (match step baseParams { known with mesh := [(ta, [pa, pb, pc])] }
        (.rpc pa (Pb.encodeMessage (rpcOfPublish [msgOf ta [1]]))) with
     | .ok (_, acts) => delivers (msgOf ta [1]) acts = 1 &&
         sendsTo pa acts = 0 && sendsTo pb acts = 1 && sendsTo pc acts = 1
     | _ => false)

  -- A local publish records the id. A later echo of that id is not
  -- delivered and is not forwarded again. The mesh is nonempty, so a
  -- missing seen record would send the echo to `pa` and `pc`.
  r.check "core.forward.own-echo-dropped"
    (match Libp2p.Protocols.Gossipsub.Core.run baseParams
        { known with mesh := [(ta, [pa, pb, pc])] }
        [.publish (msgOf ta [1]),
         .rpc pb (Pb.encodeMessage (rpcOfPublish [msgOf ta [1]]))] with
     | .ok (_, acts) => delivers (msgOf ta [1]) acts = 0 &&
         sendsTo pa acts = 1 && sendsTo pb acts = 1 && sendsTo pc acts = 1
     | _ => false)

  -- Two payloads under `defaults` stay distinct. `strictNoSign` leaves
  -- `from` and `seqno` empty, so the spec's default id would collapse them.
  r.check "core.defaults.distinct-payloads"
    (match step defaults { known with mesh := [(ta, [pa, pb])] }
        (.rpc pa (Pb.encodeMessage (rpcOfPublish [msgOf ta [1], msgOf ta [2]]))) with
     | .ok (_, acts) => delivers (msgOf ta [1]) acts = 1 &&
         delivers (msgOf ta [2]) acts = 1 && sendsTo pb acts = 2
     | _ => false)

  -- A publish without a subscription fills the fanout and forwards.
  r.check "core.publish.fanout"
    (match step baseParams { known with topics := [] } (.publish (msgOf ta [1])) with
     | .ok (s', acts) => (fanoutOf s' ta).length = 2 && publishCount acts = 2
     | _ => false)

  -- A cached id answers an IWANT with one publish.
  r.check "core.iwant.cached-answer"
    (match step baseParams
        { known with mcache := (Cache.MessageCache.empty baseParams.window).put ⟨[7]⟩ (msgOf ta [7]) }
        (.rpc pa (Pb.encodeMessage (iwantRpc [⟨[7]⟩]))) with
     | .ok (_, acts) => publishCount acts = 1
     | _ => false)

  -- The transcript driver runs two events in order and appends the
  -- actions.
  r.check "core.run.transcript"
    (match Libp2p.Protocols.Gossipsub.Core.run baseParams known
        [.subscribe ta, .publish (msgOf ta [1])] with
     | .ok (s', acts) => graftCount ta acts = 2 && publishCount acts = 2 &&
         meshIs s' ta [pa, pb]
     | _ => false)

end Tests.Gossipsub.Core
