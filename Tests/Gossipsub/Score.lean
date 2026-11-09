import Tests.Support
import Libp2p.Protocols.Gossipsub.Score

/-!
# Gossipsub suite: Score

The checks of `Libp2p.Protocols.Gossipsub.Score`. One fixed parameter set drives a regression
walk of the score function, its strict boundaries, and the validity rejections. Each expected
number carries its hand computation.

The fixed-point scale is 1000, so a weight of 1000 is 1.0 and a weight of -100 is -0.1. The
walk's topic `"eth"` carries these values: `topicWeight` 1000, `timeInMeshWeight` 10,
`timeInMeshQuantum` 1000 ms, `timeInMeshCap` 100, `firstMessageDeliveriesWeight` 10,
`firstMessageDeliveriesDecay` 500, `firstMessageDeliveriesCap` 10, `meshMessageDeliveriesWeight`
-100, `meshMessageDeliveriesDecay` 500, `meshMessageDeliveriesThreshold` 4,
`meshMessageDeliveriesCap` 10, `meshMessageDeliveriesActivation` 20000 ms,
`meshMessageDeliveriesWindow` 10 ms, `meshFailurePenaltyWeight` -100,
`meshFailurePenaltyDecay` 500, `invalidMessageDeliveriesWeight` -1000, and
`invalidMessageDeliveriesDecay` 500. The global table carries `appSpecificWeight` 1,
`ipColocationFactorWeight` -100, `ipColocationFactorThreshold` 2, `behaviourPenaltyWeight`
-100, `behaviourPenaltyThreshold` 0, `behaviourPenaltyDecay` 500, `decayInterval` 1000 ms,
`decayToZero` 1, and `topicScoreCap` 10000.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Score

open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Score

/-- The topic of the walk. -/
private def eth : TopicId := ⟨"eth"⟩

/-- A topic with no configured parameters. -/
private def other : TopicId := ⟨"other"⟩

/-- The per-topic parameters of the walk. -/
private def ethParams : TopicParams where
  topicWeight := 1000
  timeInMeshWeight := 10
  timeInMeshQuantum := 1000
  timeInMeshCap := 100
  firstMessageDeliveriesWeight := 10
  firstMessageDeliveriesDecay := 500
  firstMessageDeliveriesCap := 10
  meshMessageDeliveriesWeight := -100
  meshMessageDeliveriesDecay := 500
  meshMessageDeliveriesThreshold := 4
  meshMessageDeliveriesCap := 10
  meshMessageDeliveriesActivation := 20000
  meshMessageDeliveriesWindow := 10
  meshFailurePenaltyWeight := -100
  meshFailurePenaltyDecay := 500
  invalidMessageDeliveriesWeight := -1000
  invalidMessageDeliveriesDecay := 500

/-- The global parameters of the walk. The behavior threshold is 0, so the first penalty point
already contributes one squared point. -/
private def walkGlobal : GlobalParams where
  appSpecificWeight := 1
  ipColocationFactorWeight := -100
  ipColocationFactorThreshold := 2
  behaviourPenaltyWeight := -100
  behaviourPenaltyThreshold := 0
  behaviourPenaltyDecay := 500
  decayInterval := 1000
  decayToZero := 1
  topicScoreCap := 10000

/-- The parameters of the walk. Only `"eth"` is configured. -/
private def walkParams : Params where
  topics := fun id => if id = eth then some ethParams else none
  global := walkGlobal

/-! ## The regression walk

Each step applies one update to the state of the step before.
-/

/-- Step 2: the peer is grafted at time 0. -/
private def s1 : PeerState := graft PeerState.zero 0 eth

/-- Step 3: one mesh delivery and one first delivery. -/
private def s2 : PeerState := firstDelivery walkParams (meshDelivery walkParams s1 eth) eth

/-- Step 4: two more mesh deliveries, so the count is 3, one below the threshold 4. -/
private def s3 : PeerState :=
  meshDelivery walkParams (meshDelivery walkParams s2 eth) eth

/-- Step 5: one invalid delivery. -/
private def s4 : PeerState := invalidDelivery walkParams s3 eth

/-- Step 6: one behavior penalty. -/
private def s5 : PeerState := behaviourPenalty s4

/-- Step 7: a prune at time 30000, with the delivery deficit of 1 square. -/
private def s6 : PeerState := prune walkParams s5 30000 eth

/-- Step 8: one decay interval. -/
private def s7 : PeerState := decay walkParams s6

/-! ## Strictness fixtures -/

/-- Counters with the peer in the mesh since time 0 and no deliveries. -/
private def meshCounters : TopicCounters :=
  { TopicCounters.zero with inMesh := true, graftTime := 0 }

/-- The per-topic parameters of the topic cap checks. Only `P2` contributes, at weight 1. -/
private def capTopic : TopicParams :=
  { ethParams with
    timeInMeshWeight := 0
    firstMessageDeliveriesWeight := 1
    meshMessageDeliveriesWeight := 0
    meshFailurePenaltyWeight := 0
    invalidMessageDeliveriesWeight := 0 }

/-- The parameters of the topic cap checks: a cap of 5 and the `capTopic` table. -/
private def capParams : Params where
  topics := fun id => if id = eth then some capTopic else none
  global := { walkGlobal with topicScoreCap := 5 }

/-- A state with `n` first message deliveries in `"eth"` and no other input. -/
private def capState (n : Nat) : PeerState where
  topics := [(eth, { TopicCounters.zero with firstMessageDeliveries := n })]
  appScore := 0
  ipColocation := 0
  behaviourPenalty := 0

/-! ## Rejection fixtures

Each fixture changes one field of the valid walk parameter set.
-/

private def badP2Weight : TopicParams :=
  { ethParams with firstMessageDeliveriesWeight := -1 }

private def badP3Weight : TopicParams :=
  { ethParams with meshMessageDeliveriesWeight := 1 }

private def badP4Weight : TopicParams :=
  { ethParams with invalidMessageDeliveriesWeight := 1 }

private def badTopicWeight : TopicParams :=
  { ethParams with topicWeight := -1 }

private def badQuantum : TopicParams :=
  { ethParams with timeInMeshQuantum := 0 }

private def badDecay : TopicParams :=
  { ethParams with firstMessageDeliveriesDecay := scoreScale + 1 }

private def badP6Weight : GlobalParams :=
  { walkGlobal with ipColocationFactorWeight := 1 }

private def badP7Weight : GlobalParams :=
  { walkGlobal with behaviourPenaltyWeight := 1 }

private def badIpThreshold : GlobalParams :=
  { walkGlobal with ipColocationFactorThreshold := 0 }

/-! ## The compiled rejection proofs

Each `example` proves the rejection at compile time. The runtime check beside it names the same
case in the suite output.
-/

example : TopicParams.Valid ethParams :=
  (TopicParams.validB_iff ethParams).mp (by decide)

example : GlobalParams.Valid walkGlobal :=
  (GlobalParams.validB_iff walkGlobal).mp (by decide)

/-- The walk parameter set passes `Params.Valid`. -/
example : Params.Valid walkParams := by
  refine ⟨?_, ?_⟩
  · intro id tp h
    by_cases hid : id = eth
    · subst id
      simp [walkParams] at h
      rw [← h]
      exact (TopicParams.validB_iff ethParams).mp (by decide)
    · simp [walkParams, hid] at h
  · exact (GlobalParams.validB_iff walkGlobal).mp (by decide)

/-- A topic parameter set that the Boolean mirror rejects makes every parameters value that
configures it invalid. -/
private theorem paramsValid_of_topic_validB_false {tp : TopicParams}
    (hbad : tp.validB = false) :
    ¬ Params.Valid { topics := fun _ => some tp, global := walkGlobal } := by
  intro h
  have hb := (TopicParams.validB_iff tp).mpr (h.topic eth tp rfl)
  rw [hbad] at hb
  cases hb

/-- A global parameter set that the Boolean mirror rejects makes every parameters value that
carries it invalid. -/
private theorem paramsValid_of_global_validB_false {g : GlobalParams}
    (hbad : g.validB = false) :
    ¬ Params.Valid { topics := walkParams.topics, global := g } := by
  intro h
  have hb := (GlobalParams.validB_iff g).mpr h.global
  rw [hbad] at hb
  cases hb

example : ¬ Params.Valid
    { topics := fun _ => some badP2Weight, global := walkGlobal } :=
  paramsValid_of_topic_validB_false (by decide)

example : ¬ Params.Valid
    { topics := fun _ => some badP3Weight, global := walkGlobal } :=
  paramsValid_of_topic_validB_false (by decide)

example : ¬ Params.Valid
    { topics := fun _ => some badP4Weight, global := walkGlobal } :=
  paramsValid_of_topic_validB_false (by decide)

example : ¬ Params.Valid
    { topics := fun _ => some badTopicWeight, global := walkGlobal } :=
  paramsValid_of_topic_validB_false (by decide)

example : ¬ Params.Valid
    { topics := fun _ => some badQuantum, global := walkGlobal } :=
  paramsValid_of_topic_validB_false (by decide)

example : ¬ Params.Valid
    { topics := fun _ => some badDecay, global := walkGlobal } :=
  paramsValid_of_topic_validB_false (by decide)

example : ¬ Params.Valid { topics := walkParams.topics, global := badP6Weight } :=
  paramsValid_of_global_validB_false (by decide)

example : ¬ Params.Valid { topics := walkParams.topics, global := badP7Weight } :=
  paramsValid_of_global_validB_false (by decide)

example : ¬ Params.Valid { topics := walkParams.topics, global := badIpThreshold } :=
  paramsValid_of_global_validB_false (by decide)

/-- Run the checks of this module. -/
def run (r : Runner) : IO Unit := do
  r.section "gossipsub Score" "vendor/specs/pubsub"

  -- Step 1: the fresh peer. Every term is 0 and the topic list is empty.
  r.check "score.walk.fresh-peer" (score walkParams PeerState.zero 0 == 0)

  -- Step 2: graft at time 0, scored at 10000. Elapsed mesh time 10000 ms gives P1 = 10000 /
  -- 1000 = 10, capped at 100, so 10. P3 is 0 because the activation is 20000 ms. Topic score
  -- = 10 * 10 + 10 * 0 + (-100) * 0 + (-100) * 0 + (-1000) * 0 = 100. Topic contribution =
  -- 1000 * 100 tdiv 1000 = 100. Total = 100.
  r.check "score.walk.graft" (score walkParams s1 10000 == 100)

  -- Step 3: one mesh delivery and one first delivery, scored at 10000. P1 = 10, P2 = 1, so the
  -- topic score = 100 + 10 * 1 = 110. Contribution = 110. Total = 110.
  r.check "score.walk.deliveries" (score walkParams s2 10000 == 110)

  -- Step 4: two more mesh deliveries, so the count is 3, scored at 30000. Elapsed = 30000,
  -- P1 = 30, so 300. P3 applies because 20000 < 30000 and 3 < 4: deficit 1, square 1, term
  -- = -100 * 1 = -100. Topic score = 300 + 10 - 100 = 210. Contribution = 210. Total = 210.
  r.check "score.walk.p3" (score walkParams s3 30000 == 210)

  -- Step 5: one invalid delivery, scored at 30000. P4 = 1 * 1 = 1, term = -1000. Topic score
  -- = 210 - 1000 = -790. Contribution = -790. Total = -790.
  r.check "score.walk.p4" (score walkParams s4 30000 == -790)

  -- Step 6: one behavior penalty, scored at 30000. The threshold is 0, so P7 = (1 - 0)^2 = 1,
  -- global term = -100 * 1 = -100. Total = -790 - 100 = -890.
  r.check "score.walk.p7" (score walkParams s5 30000 == -890)

  -- Step 7: prune at 30000. The elapsed time 30000 passes the activation, and the count 3 is
  -- below the threshold 4, so the failure penalty grows by (4 - 3)^2 = 1. P1 = 300, P2 = 10,
  -- P3 = -100, P3b = -100 * 1 = -100, P4 = -1000: topic score = -890. Global P7 = -100.
  -- Total = -990.
  r.check "score.walk.prune" (score walkParams s6 30000 == -990)

  -- Step 8: one decay. Each factor is 500, so a counter c becomes c * 500 / 1000, and a result
  -- below 1 becomes 0. First deliveries 1 -> 0, mesh deliveries 3 -> 1, failure penalty 1 -> 0,
  -- invalid deliveries 1 -> 0, behavior penalty 1 -> 0. The mesh time and the membership stay.
  r.check "score.walk.decay.first-message-deliveries"
    ((countersOf s7 eth).firstMessageDeliveries == 0)
  r.check "score.walk.decay.mesh-message-deliveries"
    ((countersOf s7 eth).meshMessageDeliveries == 1)
  r.check "score.walk.decay.mesh-failure-penalty"
    ((countersOf s7 eth).meshFailurePenalty == 0)
  r.check "score.walk.decay.invalid-message-deliveries"
    ((countersOf s7 eth).invalidMessageDeliveries == 0)
  r.check "score.walk.decay.behavior-penalty" (s7.behaviourPenalty == 0)
  r.check "score.walk.decay.keeps-mesh-time"
    ((countersOf s7 eth).timeInMesh == 30000 && (countersOf s7 eth).inMesh == false)

  -- Step 9: score after the decay, at 30000. P1 = 300, P2 = 0, P3 = (4 - 1)^2 = 9 with term
  -- -900, P3b = 0, P4 = 0. Topic score = 300 - 900 = -600. Contribution = -600. Global P7 = 0.
  -- Total = -600.
  r.check "score.walk.final" (score walkParams s7 30000 == -600)

  -- The P3 activation boundary. At 20000 ms the activation is equal, so the strict comparison
  -- fails and P3 = 0. At 20001 ms the deficit is (4 - 0)^2 = 16.
  r.check "score.p3.activation-boundary"
    (p3 ethParams 20000 meshCounters == 0 && p3 ethParams 20001 meshCounters == 16)

  -- The P3 threshold boundary. At the count 4 the strict comparison fails and P3 = 0. At 3 the
  -- deficit is 1 and P3 = 1.
  r.check "score.p3.threshold-boundary"
    (p3 ethParams 30000 { meshCounters with meshMessageDeliveries := 4 } == 0 &&
      p3 ethParams 30000 { meshCounters with meshMessageDeliveries := 3 } == 1)

  -- The decay zero boundary. A counter equal to `decayToZero` with a full decay stays at 1. A
  -- counter one below becomes 0.
  r.check "score.decay.zero-boundary"
    (decayCounter 1000 1 1 == 1 && decayCounter 1000 1 0 == 0)

  -- The P1 cap boundary. Elapsed 100000 ms gives 100 points, equal to the cap, so P1 = 100. One
  -- quantum more gives 101 points, and the cap holds P1 at 100.
  r.check "score.p1.cap-boundary"
    (p1 ethParams 100000 meshCounters == 100 && p1 ethParams 101000 meshCounters == 100)

  -- The P6 threshold boundary. Colocation 2 equals the threshold, so P6 = 0. Colocation 3 gives
  -- the surplus 1 squared.
  r.check "score.p6.threshold-boundary"
    (p6 walkGlobal { PeerState.zero with ipColocation := 2 } == 0 &&
      p6 walkGlobal { PeerState.zero with ipColocation := 3 } == 1)

  -- The P7 threshold boundary. Penalty 0 equals the threshold, so P7 = 0. Penalty 1 gives the
  -- excess 1 squared.
  r.check "score.p7.threshold-boundary"
    (p7 walkGlobal { PeerState.zero with behaviourPenalty := 0 } == 0 &&
      p7 walkGlobal { PeerState.zero with behaviourPenalty := 1 } == 1)

  -- The topic cap boundary. With `P2` at weight 1 and no other term, the raw topic part equals
  -- the delivery count. At 5 the raw part equals the cap 5 and stays. At 6 the raw part 6 is
  -- above the cap, so the topic part is 5.
  r.check "score.topic-cap-boundary"
    (topicPart capParams 0 (capState 5) == 5 && topicPart capParams 0 (capState 6) == 5)

  -- The cap applies at increment time. A first delivery from 9 reaches the cap 10, and one more
  -- from 10 leaves the counter at 10.
  r.check "score.cap-at-increment"
    ((countersOf (firstDelivery walkParams (capState 9) eth) eth).firstMessageDeliveries == 10 &&
      (countersOf (firstDelivery walkParams (capState 10) eth) eth).firstMessageDeliveries == 10)

  -- A delivery to a topic with no parameters leaves the score alone. The state s3 scores 210 at
  -- 30000, and the first delivery to `"other"` is a no-op.
  r.check "score.unconfigured-topic-ignored"
    (score walkParams (firstDelivery walkParams s3 other) 30000 ==
      score walkParams s3 30000)

  -- The rejections. Each Boolean mirror is false, and the `example` beside the definition
  -- proves the predicate rejects the same value.
  r.check "score.valid.reject-negative-p2-weight" (!badP2Weight.validB)
  r.check "score.valid.reject-positive-p3-weight" (!badP3Weight.validB)
  r.check "score.valid.reject-positive-p4-weight" (!badP4Weight.validB)
  r.check "score.valid.reject-negative-topic-weight" (!badTopicWeight.validB)
  r.check "score.valid.reject-zero-quantum" (!badQuantum.validB)
  r.check "score.valid.reject-decay-above-scale" (!badDecay.validB)
  r.check "score.valid.reject-positive-p6-weight" (!badP6Weight.validB)
  r.check "score.valid.reject-positive-p7-weight" (!badP7Weight.validB)
  r.check "score.valid.reject-zero-ip-threshold" (!badIpThreshold.validB)

  -- A zero P6 weight and a zero P7 weight are valid: the predicate requires `<= 0`. The
  -- walk's global table already carries a zero behavior threshold, and a zero weight is also
  -- accepted.
  r.check "score.valid.accept-zero-p6-p7-weight"
    ({ walkGlobal with ipColocationFactorWeight := 0, behaviourPenaltyWeight := 0 } :
      GlobalParams).validB

end Tests.Gossipsub.Score
