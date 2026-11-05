import Libp2p.Protocols.Gossipsub.Types

/-!
# Gossipsub peer scoring

The peer score function of gossipsub v1.1 over its counters, with decay. The function is pure.
The caller passes the time as `Millis`, and this module reads no clock.

## The score of the spec

The spec mixes four per-topic terms with three global terms
(`vendor/specs/pubsub/gossipsub/gossipsub-v1.1.md`, section "Peer Scoring"):

`Score = TopicCap(sum over topics t * (w1*P1 + w2*P2 + w3*P3 + w3b*P3b + w4*P4))
  + w5*P5 + w6*P6 + w7*P7`

`P1` is the time in mesh, `P2` the first message deliveries, `P3` the mesh message delivery rate,
`P3b` the mesh message delivery failures, `P4` the invalid message deliveries, `P5` the
application score, `P6` the IP colocation factor, and `P7` the behavior penalty. The topic cap
applies to the sum of the topic terms. A topic with no configured parameters contributes nothing.

## Fixed point

The spec computes with float64. This module computes with integers, in `scoreScale` units per 1.0
(`Gossipsub/Types.lean`). One convention applies to every product:

- Every weight is an `Int` in `1/scoreScale` units. A weight of 3 means 0.003.
- The `P1` to `P4`, `P6`, and `P7` values are `Nat` counts.
- A weight times a count is an exact `Int` product.
- The one rounded product is the topic contribution:
  `(topicWeight * topicScore) tdiv scoreScale`. `Int.tdiv` truncates toward zero. This is the
  single rounding site.
- The decay divides with `Nat` division, `counter * decay / scoreScale`, which floors.

Lean 4.34 defines `/` on `Int` as Euclidean division. For a negative numerator, `/ scoreScale`
rounds down by one unit at the boundary, and `Int.tdiv scoreScale` truncates toward zero. This
module writes `Int.tdiv` to keep the truncation toward zero that the fixed-point convention
states.

## Parameters and validity

`Params.Valid` carries the weight signs and the decay bounds that the score theorems consume,
plus three constraints that no theorem consumes. The predicate adds `topicWeight >= 0` and
`timeInMeshQuantum > 0` to the weight and decay list, because a negative topic weight inverts
every term of its topic. It also carries `ipColocationFactorThreshold >= 1` and
`appSpecificWeight >= 0` from the spec's global table. The `TopicParams.Valid` docstring lists
the constraints and names the spec constraint that the predicate does not encode. The predicate
is a sufficient condition for the theorems, and it is not the complete parameter table of the
spec.

## The behavior penalty threshold

The vendored spec describes `P7` as the square of a counter with no threshold. The global
parameter table names only `BehaviourPenaltyWeight` and `BehaviourPenaltyDecay`. This module
carries `behaviourPenaltyThreshold`, as the go implementation does, and `P7` is the square of the
excess of the counter over the threshold. A threshold of 0 reproduces the spec's square of the
counter.

## Application score

`PeerState.appScore` is an integer count of application points. The spec leaves the unit of `P5`
open. An integer count keeps the product `appSpecificWeight * appScore` exact.

## Decay

`decayCounter` zeroes a counter that falls below `decayToZero` and keeps a counter that equals it.
The comparison is strict, as the spec's pseudocode writes it.

## Time

`elapsed` computes the mesh time lazily from `timeInMesh`, `graftTime`, and `now`. `Nat`
subtraction saturates at zero. The caller passes `now >= graftTime`; no theorem consumes that
precondition.

## The Boolean validity mirror

`TopicParams.validB` and `GlobalParams.validB` repeat the sign lists of the predicates as
`Bool` values. The test runner takes `Bool`, and `Params.Valid` has a `∀` over `TopicId`, so no
`Decidable` instance exists. The reflection theorems tie each `Bool` mirror to its predicate.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Score

/-! ## Parameters -/

/-- The per-topic score parameters of gossipsub v1.1. The field order follows the topic
parameter table of the spec. `meshMessageDeliveriesWindow` and `meshMessageDeliveriesActivation`
feed the core's delivery accounting; `topicScore` reads only the activation. -/
structure TopicParams where
  /-- The weight of this topic in the total score. -/
  topicWeight : Int
  /-- The weight of `P1`, the time in mesh. -/
  timeInMeshWeight : Int
  /-- The mesh time that earns one `P1` point. -/
  timeInMeshQuantum : Millis
  /-- The maximum of `P1`. -/
  timeInMeshCap : Nat
  /-- The weight of `P2`, the first message deliveries. -/
  firstMessageDeliveriesWeight : Int
  /-- The decay factor of the `P2` counter. -/
  firstMessageDeliveriesDecay : Nat
  /-- The maximum of the `P2` counter. The cap applies at increment time. -/
  firstMessageDeliveriesCap : Nat
  /-- The weight of `P3`, the mesh message delivery rate. -/
  meshMessageDeliveriesWeight : Int
  /-- The decay factor of the `P3` counter. -/
  meshMessageDeliveriesDecay : Nat
  /-- The delivery count below which `P3` penalizes the peer. -/
  meshMessageDeliveriesThreshold : Nat
  /-- The maximum of the `P3` counter. The cap applies at increment time. -/
  meshMessageDeliveriesCap : Nat
  /-- The mesh time a peer needs before `P3` applies. -/
  meshMessageDeliveriesActivation : Millis
  /-- The window after a first delivery that counts as a near-first delivery. -/
  meshMessageDeliveriesWindow : Millis
  /-- The weight of `P3b`, the mesh failure penalty. -/
  meshFailurePenaltyWeight : Int
  /-- The decay factor of the `P3b` counter. -/
  meshFailurePenaltyDecay : Nat
  /-- The weight of `P4`, the invalid message deliveries. -/
  invalidMessageDeliveriesWeight : Int
  /-- The decay factor of the `P4` counter. -/
  invalidMessageDeliveriesDecay : Nat

/-- The global score parameters of gossipsub v1.1. The field order follows the global parameter
table of the spec. `decayInterval` feeds the core's heartbeat; `score` does not read it.

The vendored spec gives `P7` as the square of a counter with no threshold
(`gossipsub-v1.1.md`, "The Score Function"). The global parameter table names only
`BehaviourPenaltyWeight` and `BehaviourPenaltyDecay`. This module carries
`behaviourPenaltyThreshold`, as the go implementation does. -/
structure GlobalParams where
  /-- The weight of `P5`, the application score. -/
  appSpecificWeight : Int
  /-- The weight of `P6`, the IP colocation factor. -/
  ipColocationFactorWeight : Int
  /-- The colocation count at or below which `P6` is zero. -/
  ipColocationFactorThreshold : Nat
  /-- The weight of `P7`, the behavior penalty. -/
  behaviourPenaltyWeight : Int
  /-- The behavior penalty count at or below which `P7` is zero. -/
  behaviourPenaltyThreshold : Nat
  /-- The decay factor of the behavior penalty counter. -/
  behaviourPenaltyDecay : Nat
  /-- The decay period of the router's heartbeat. -/
  decayInterval : Millis
  /-- The counter limit below which a decayed counter becomes zero. -/
  decayToZero : Nat
  /-- The cap of the summed topic part. A cap of 0 or less means no cap. -/
  topicScoreCap : Int

/-- The score parameters: the per-topic table and the global table. -/
structure Params where
  /-- The parameters of each configured topic; `none` means the topic is not configured. -/
  topics : TopicId → Option TopicParams
  /-- The global parameters. -/
  global : GlobalParams

/-! ## Validity -/

/-- The validity predicate of a topic's parameters. It carries the weight signs that the score
theorems consume, the decay bounds that the decay theorems consume, and one constraint that no
theorem consumes:

- `topicWeight_nonneg`: a negative topic weight inverts every term of the topic. The invalid
  delivery monotonicity theorem consumes it.
- `timeInMeshQuantum_pos`: the quantum divides the elapsed mesh time. No theorem consumes this
  constraint, and it is part of the contract the core relies on.
- The four decay bounds keep each factor at or below `scoreScale`, the unit of a full decay.
  Each decay theorem consumes the bound of its own counter.

The spec's `MeshMessageDeliveriesCap >= MeshMessageDeliveriesThreshold` constraint is not
encoded. -/
structure TopicParams.Valid (tp : TopicParams) : Prop where
  /-- The topic weight is at or above 0. -/
  topicWeight_nonneg : 0 ≤ tp.topicWeight
  /-- The `P1` weight is at or above 0. -/
  timeInMeshWeight_nonneg : 0 ≤ tp.timeInMeshWeight
  /-- The `P2` weight is at or above 0. -/
  firstMessageDeliveriesWeight_nonneg : 0 ≤ tp.firstMessageDeliveriesWeight
  /-- The `P3` weight is at or below 0. -/
  meshMessageDeliveriesWeight_nonpos : tp.meshMessageDeliveriesWeight ≤ 0
  /-- The `P3b` weight is at or below 0. -/
  meshFailurePenaltyWeight_nonpos : tp.meshFailurePenaltyWeight ≤ 0
  /-- The `P4` weight is at or below 0. -/
  invalidMessageDeliveriesWeight_nonpos : tp.invalidMessageDeliveriesWeight ≤ 0
  /-- The time quantum is at or above 1 millisecond. -/
  timeInMeshQuantum_pos : 0 < tp.timeInMeshQuantum
  /-- The `P2` decay factor is at most a full decay. -/
  firstMessageDeliveriesDecay_le : tp.firstMessageDeliveriesDecay ≤ scoreScale
  /-- The `P3` decay factor is at most a full decay. -/
  meshMessageDeliveriesDecay_le : tp.meshMessageDeliveriesDecay ≤ scoreScale
  /-- The `P3b` decay factor is at most a full decay. -/
  meshFailurePenaltyDecay_le : tp.meshFailurePenaltyDecay ≤ scoreScale
  /-- The `P4` decay factor is at most a full decay. -/
  invalidMessageDeliveriesDecay_le : tp.invalidMessageDeliveriesDecay ≤ scoreScale

/-- The validity predicate of the global parameters. It carries the weight signs that the score
theorems consume, the colocation threshold of the spec, and the behavior decay bound.

`appSpecificWeight_nonneg` and `ipColocationFactorThreshold_pos` are spec constraints, and no
theorem consumes them. -/
structure GlobalParams.Valid (g : GlobalParams) : Prop where
  /-- The `P5` weight is at or above 0. -/
  appSpecificWeight_nonneg : 0 ≤ g.appSpecificWeight
  /-- The `P6` weight is at or below 0. -/
  ipColocationFactorWeight_nonpos : g.ipColocationFactorWeight ≤ 0
  /-- The colocation threshold is at least 1. -/
  ipColocationFactorThreshold_pos : 1 ≤ g.ipColocationFactorThreshold
  /-- The `P7` weight is at or below 0. -/
  behaviourPenaltyWeight_nonpos : g.behaviourPenaltyWeight ≤ 0
  /-- The behavior penalty decay factor is at most a full decay. -/
  behaviourPenaltyDecay_le : g.behaviourPenaltyDecay ≤ scoreScale

/-- The validity predicate of the parameters: every configured topic passes
`TopicParams.Valid`, and the global parameters pass `GlobalParams.Valid`. An unconfigured topic
passes vacuously. -/
structure Params.Valid (p : Params) : Prop where
  /-- Every configured topic is valid. -/
  topic : ∀ (id : TopicId) (tp : TopicParams), p.topics id = some tp → TopicParams.Valid tp
  /-- The global parameters are valid. -/
  global : GlobalParams.Valid p.global

/-- The `Bool` mirror of `TopicParams.Valid`. The test runner takes `Bool`, and a `Prop`
structure has no `Decidable` instance. `TopicParams.validB_iff` ties the mirror to the
predicate. -/
def TopicParams.validB (tp : TopicParams) : Bool :=
  decide (0 ≤ tp.topicWeight) &&
  decide (0 ≤ tp.timeInMeshWeight) &&
  decide (0 ≤ tp.firstMessageDeliveriesWeight) &&
  decide (tp.meshMessageDeliveriesWeight ≤ 0) &&
  decide (tp.meshFailurePenaltyWeight ≤ 0) &&
  decide (tp.invalidMessageDeliveriesWeight ≤ 0) &&
  decide (0 < tp.timeInMeshQuantum) &&
  decide (tp.firstMessageDeliveriesDecay ≤ scoreScale) &&
  decide (tp.meshMessageDeliveriesDecay ≤ scoreScale) &&
  decide (tp.meshFailurePenaltyDecay ≤ scoreScale) &&
  decide (tp.invalidMessageDeliveriesDecay ≤ scoreScale)

/-- The `Bool` mirror of `GlobalParams.Valid`. -/
def GlobalParams.validB (g : GlobalParams) : Bool :=
  decide (0 ≤ g.appSpecificWeight) &&
  decide (g.ipColocationFactorWeight ≤ 0) &&
  decide (1 ≤ g.ipColocationFactorThreshold) &&
  decide (g.behaviourPenaltyWeight ≤ 0) &&
  decide (g.behaviourPenaltyDecay ≤ scoreScale)

/-- The `Bool` mirror accepts exactly the valid topic parameters. -/
theorem TopicParams.validB_iff (tp : TopicParams) :
    tp.validB = true ↔ TopicParams.Valid tp := by
  constructor
  · intro h
    simp [TopicParams.validB, Bool.and_eq_true, decide_eq_true_eq] at h
    constructor <;> simp_all
  · intro h
    cases h
    simp [TopicParams.validB, *]

/-- The `Bool` mirror accepts exactly the valid global parameters. -/
theorem GlobalParams.validB_iff (g : GlobalParams) :
    g.validB = true ↔ GlobalParams.Valid g := by
  constructor
  · intro h
    simp [GlobalParams.validB, Bool.and_eq_true, decide_eq_true_eq] at h
    constructor <;> simp_all
  · intro h
    cases h
    simp [GlobalParams.validB, *]

/-! ## Peer state -/

/-- The counters of one peer in one topic. `timeInMesh` holds the accrued mesh time, and
`graftTime` holds the start of the current mesh period. `elapsed` sums the two when `inMesh` is
true. -/
structure TopicCounters where
  /-- The mesh time accrued in earlier mesh periods. -/
  timeInMesh : Millis
  /-- The time of the last graft. -/
  graftTime : Millis
  /-- Whether the peer is in the mesh of the topic. -/
  inMesh : Bool
  /-- The first message deliveries, capped at increment time. -/
  firstMessageDeliveries : Nat
  /-- The mesh message deliveries, capped at increment time. -/
  meshMessageDeliveries : Nat
  /-- The mesh message delivery failures. -/
  meshFailurePenalty : Nat
  /-- The invalid message deliveries. -/
  invalidMessageDeliveries : Nat

/-- The all-zero counters of a peer that has no history in a topic. -/
def TopicCounters.zero : TopicCounters where
  timeInMesh := 0
  graftTime := 0
  inMesh := false
  firstMessageDeliveries := 0
  meshMessageDeliveries := 0
  meshFailurePenalty := 0
  invalidMessageDeliveries := 0

/-- The score state of one peer: the per-topic counters and the three global inputs. -/
structure PeerState where
  /-- The counters of each topic the peer has a history in. -/
  topics : List (TopicId × TopicCounters)
  /-- The application score `P5`, an integer count of application points. -/
  appScore : Int
  /-- The IP colocation count `P6`. -/
  ipColocation : Nat
  /-- The behavior penalty counter `P7`. -/
  behaviourPenalty : Nat

/-- The state of a fresh peer: no topic history, no application score, no colocation, and no
behavior penalty. -/
def PeerState.zero : PeerState where
  topics := []
  appScore := 0
  ipColocation := 0
  behaviourPenalty := 0

/-! ## Scoring -/

/-- The mesh time of a peer in a topic. The peer accrues time from `graftTime` to `now` while
`inMesh` is true, and the stored `timeInMesh` holds the earlier periods. The `Nat` subtraction
saturates at zero. The caller passes `now >= graftTime`. -/
def elapsed (now : Millis) (t : TopicCounters) : Millis :=
  t.timeInMesh + (if t.inMesh then now - t.graftTime else 0)

/-- `P1`, the time in mesh: the elapsed time in quanta, capped. -/
def p1 (tp : TopicParams) (now : Millis) (t : TopicCounters) : Nat :=
  min (elapsed now t / tp.timeInMeshQuantum) tp.timeInMeshCap

/-- `P3`, the mesh message delivery rate: the square of the delivery deficit below the
threshold, when the activation window has passed. Both comparisons are strict, so equality with
either bound gives 0. -/
def p3 (tp : TopicParams) (now : Millis) (t : TopicCounters) : Nat :=
  if tp.meshMessageDeliveriesActivation < elapsed now t ∧
      t.meshMessageDeliveries < tp.meshMessageDeliveriesThreshold then
    (tp.meshMessageDeliveriesThreshold - t.meshMessageDeliveries) *
      (tp.meshMessageDeliveriesThreshold - t.meshMessageDeliveries)
  else 0

/-- `P4`, the invalid message deliveries: the square of the counter, uncapped. -/
def p4 (t : TopicCounters) : Nat :=
  t.invalidMessageDeliveries * t.invalidMessageDeliveries

/-- `P6`, the IP colocation factor: the square of the surplus over the threshold. -/
def p6 (g : GlobalParams) (s : PeerState) : Nat :=
  if g.ipColocationFactorThreshold < s.ipColocation then
    (s.ipColocation - g.ipColocationFactorThreshold) *
      (s.ipColocation - g.ipColocationFactorThreshold)
  else 0

/-- `P7`, the behavior penalty: the square of the excess over the threshold. -/
def p7 (g : GlobalParams) (s : PeerState) : Nat :=
  if g.behaviourPenaltyThreshold < s.behaviourPenalty then
    (s.behaviourPenalty - g.behaviourPenaltyThreshold) *
      (s.behaviourPenalty - g.behaviourPenaltyThreshold)
  else 0

/-- The per-topic score: the weighted sum of the five terms, in `1/scoreScale` weight units.
The `P2` and `P3b` caps apply at increment time, so this function reads the counters as they
stand. -/
def topicScore (tp : TopicParams) (now : Millis) (t : TopicCounters) : Int :=
  tp.timeInMeshWeight * (p1 tp now t : Int)
  + tp.firstMessageDeliveriesWeight * (t.firstMessageDeliveries : Int)
  + tp.meshMessageDeliveriesWeight * (p3 tp now t : Int)
  + tp.meshFailurePenaltyWeight * (t.meshFailurePenalty : Int)
  + tp.invalidMessageDeliveriesWeight * (p4 t : Int)

/-- The contribution of one topic entry. An unconfigured topic contributes 0. A configured
topic contributes `(topicWeight * topicScore) tdiv scoreScale`; this is the one rounding site of
the module. -/
private def topicContribution (p : Params) (now : Millis)
    (entry : TopicId × TopicCounters) : Int :=
  match p.topics entry.1 with
  | some tp => (tp.topicWeight * topicScore tp now entry.2).tdiv scoreScale
  | none => 0

/-- The sum of the topic contributions, before the cap. -/
private def rawTopicPart (p : Params) (now : Millis) (s : PeerState) : Int :=
  (s.topics.map (topicContribution p now)).sum

/-- The topic part of the score: the sum of the configured topic contributions, capped at
`topicScoreCap` when the cap is positive. A cap of 0 or less means no cap. -/
def topicPart (p : Params) (now : Millis) (s : PeerState) : Int :=
  let raw := rawTopicPart p now s
  if 0 < p.global.topicScoreCap ∧ p.global.topicScoreCap < raw then
    p.global.topicScoreCap
  else raw

/-- The peer score of gossipsub v1.1: the capped topic part, the weighted application score, and
the weighted `P6` and `P7` terms. The last three products are exact. -/
def score (p : Params) (s : PeerState) (now : Millis) : Score :=
  topicPart p now s
  + p.global.appSpecificWeight * s.appScore
  + p.global.ipColocationFactorWeight * (p6 p.global s : Int)
  + p.global.behaviourPenaltyWeight * (p7 p.global s : Int)

/-! ## Decay -/

/-- One decay step of a counter: multiply by the decay factor, divide by `scoreScale`, and
zero the result when it falls below `decayToZero`. The comparison is strict. -/
def decayCounter (d : Nat) (decayToZero : Nat) (c : Nat) : Nat :=
  if c * d / scoreScale < decayToZero then 0 else c * d / scoreScale

/-- One decay step of the topic counters. The four decaying counters move; `timeInMesh`,
`graftTime`, and `inMesh` stay. -/
def decayTopic (tp : TopicParams) (decayToZero : Nat) (t : TopicCounters) : TopicCounters :=
  { t with
    firstMessageDeliveries :=
      decayCounter tp.firstMessageDeliveriesDecay decayToZero t.firstMessageDeliveries
    meshMessageDeliveries :=
      decayCounter tp.meshMessageDeliveriesDecay decayToZero t.meshMessageDeliveries
    meshFailurePenalty :=
      decayCounter tp.meshFailurePenaltyDecay decayToZero t.meshFailurePenalty
    invalidMessageDeliveries :=
      decayCounter tp.invalidMessageDeliveriesDecay decayToZero t.invalidMessageDeliveries }

/-- One decay step of a topic entry. An entry whose topic has no configured parameters stays
unchanged. Such an entry contributes 0 to the score. -/
private def decayEntry (p : Params) (decayToZero : Nat)
    (entry : TopicId × TopicCounters) : TopicId × TopicCounters :=
  match p.topics entry.1 with
  | some tp => (entry.1, decayTopic tp decayToZero entry.2)
  | none => entry

/-- One decay interval of a peer state. The four topic counters and the behavior penalty
decay. The application score and the colocation count stay; the application owns their
lifecycle. -/
def decay (p : Params) (s : PeerState) : PeerState :=
  { s with
    topics := s.topics.map (decayEntry p p.global.decayToZero)
    behaviourPenalty :=
      decayCounter p.global.behaviourPenaltyDecay p.global.decayToZero s.behaviourPenalty }

/-! ## The counter table -/

/-- The first entry of `l` with key `id`. -/
private def lookupCounters :
    List (TopicId × TopicCounters) → TopicId → Option TopicCounters
  | [], _ => none
  | (k, v) :: rest, id => if k = id then some v else lookupCounters rest id

/-- The counters of `id`, or the all-zero counters when the state has no entry for the topic. -/
def countersOf (s : PeerState) (id : TopicId) : TopicCounters :=
  match lookupCounters s.topics id with
  | some t => t
  | none => TopicCounters.zero

/-- Replace the first entry with key `id`, or append a new entry when the key is absent. The
other entries keep their order. -/
private def upsert :
    List (TopicId × TopicCounters) → TopicId → TopicCounters →
      List (TopicId × TopicCounters)
  | [], id, t => [(id, t)]
  | (k, v) :: rest, id, t =>
      if k = id then (k, t) :: rest else (k, v) :: upsert rest id t

/-- Replace the counters of `id` in the state. -/
private def setCounters (s : PeerState) (id : TopicId) (t : TopicCounters) : PeerState :=
  { s with topics := upsert s.topics id t }

/-! ## Counter updates -/

/-- The graft update: when the peer is not in the mesh, set `inMesh` and record the graft time.
A peer that is already in the mesh is unchanged. -/
def graft (s : PeerState) (now : Millis) (id : TopicId) : PeerState :=
  let t := countersOf s id
  if t.inMesh then s
  else setCounters s id { t with inMesh := true, graftTime := now }

/-- The counter part of a prune: fold the elapsed mesh time into `timeInMesh`, leave the mesh,
and add the square of the delivery deficit to the failure penalty when the activation window
has passed and the delivery count is below the threshold. -/
private def pruneCounters (p : Params) (now : Millis) (id : TopicId)
    (t : TopicCounters) : TopicCounters :=
  let e := elapsed now t
  let t1 := { t with timeInMesh := e, inMesh := false }
  match p.topics id with
  | some tp =>
      if tp.meshMessageDeliveriesActivation < e ∧
          t.meshMessageDeliveries < tp.meshMessageDeliveriesThreshold then
        { t1 with meshFailurePenalty := t.meshFailurePenalty +
            (tp.meshMessageDeliveriesThreshold - t.meshMessageDeliveries) *
              (tp.meshMessageDeliveriesThreshold - t.meshMessageDeliveries) }
      else t1
  | none => t1

/-- The prune update: a peer in the mesh folds its mesh time and adds the failure penalty, per
spec. A peer that is not in the mesh is unchanged. -/
def prune (p : Params) (s : PeerState) (now : Millis) (id : TopicId) : PeerState :=
  let t := countersOf s id
  if t.inMesh then setCounters s id (pruneCounters p now id t) else s

/-- The first message delivery update: increment the counter and cap it. An unconfigured topic
is unchanged. -/
def firstDelivery (p : Params) (s : PeerState) (id : TopicId) : PeerState :=
  match p.topics id with
  | some tp =>
      let t := countersOf s id
      setCounters s id { t with
        firstMessageDeliveries :=
          min (t.firstMessageDeliveries + 1) tp.firstMessageDeliveriesCap }
  | none => s

/-- The mesh message delivery update: increment the counter and cap it. An unconfigured topic
is unchanged. -/
def meshDelivery (p : Params) (s : PeerState) (id : TopicId) : PeerState :=
  match p.topics id with
  | some tp =>
      let t := countersOf s id
      setCounters s id { t with
        meshMessageDeliveries :=
          min (t.meshMessageDeliveries + 1) tp.meshMessageDeliveriesCap }
  | none => s

/-- The counter part of an invalid delivery: increment the uncapped `P4` counter. -/
private def invalidStep (t : TopicCounters) : TopicCounters :=
  { t with invalidMessageDeliveries := t.invalidMessageDeliveries + 1 }

/-- The invalid message delivery update: increment the uncapped `P4` counter. An unconfigured
topic is unchanged. -/
def invalidDelivery (p : Params) (s : PeerState) (id : TopicId) : PeerState :=
  match p.topics id with
  | some _ => setCounters s id (invalidStep (countersOf s id))
  | none => s

/-- The behavior penalty update: increment the `P7` counter. It is uncapped, and the decay
reduces it later. -/
def behaviourPenalty (s : PeerState) : PeerState :=
  { s with behaviourPenalty := s.behaviourPenalty + 1 }

/-! ## Table lemmas -/

/-- Reading the table after a write of the same key returns the written counters. -/
private theorem lookupCounters_upsert_same (l : List (TopicId × TopicCounters))
    (id : TopicId) (t : TopicCounters) :
    lookupCounters (upsert l id t) id = some t := by
  induction l with
  | nil => simp [upsert, lookupCounters]
  | cons head rest ih =>
      obtain ⟨k, v⟩ := head
      by_cases hk : k = id
      · simp [upsert, lookupCounters, hk]
      · simp [upsert, lookupCounters, hk, ih]

/-- Reading the table of a mapped list maps the read entry, when the map keeps the keys. -/
private theorem lookupCounters_map
    (f : TopicId × TopicCounters → TopicId × TopicCounters)
    (hf : ∀ e, (f e).1 = e.1) :
    ∀ (l : List (TopicId × TopicCounters)) (id : TopicId),
      lookupCounters (l.map f) id =
        (lookupCounters l id).map (fun t => (f (id, t)).2) := by
  intro l
  induction l with
  | nil => intro id; rfl
  | cons head rest ih =>
      intro id
      obtain ⟨k, v⟩ := head
      by_cases hk : k = id
      · simp [lookupCounters, hf, hk]
      · simp [lookupCounters, hf, hk, ih]

/-- The decay map keeps the key of every entry. -/
private theorem decayEntry_key (p : Params) (z : Nat) (e : TopicId × TopicCounters) :
    (decayEntry p z e).1 = e.1 := by
  obtain ⟨k, v⟩ := e
  unfold decayEntry
  split <;> rfl

/-- Reading the counters of a decayed state. -/
private theorem countersOf_decay (p : Params) (s : PeerState) (id : TopicId) :
    countersOf (decay p s) id =
      match lookupCounters s.topics id with
      | some t => (decayEntry p p.global.decayToZero (id, t)).2
      | none => TopicCounters.zero := by
  unfold countersOf decay
  rw [lookupCounters_map (decayEntry p p.global.decayToZero) (decayEntry_key p _)
    s.topics id]
  cases lookupCounters s.topics id <;> rfl

/-- Replacing the first matching entry does not increase a sum of contributions, when the
replacement contributes at most the old entry. -/
private theorem sum_map_upsert_le_of_found (f : TopicId × TopicCounters → Int)
    (l : List (TopicId × TopicCounters)) (id : TopicId)
    (u t : TopicCounters) (hfound : lookupCounters l id = some t)
    (hle : f (id, u) ≤ f (id, t)) :
    ((upsert l id u).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp [lookupCounters] at hfound
  | cons head rest ih =>
      obtain ⟨k, v⟩ := head
      by_cases hk : k = id
      · have hvt : v = t := by
          rw [hk] at hfound
          simpa [lookupCounters] using hfound
        subst v
        rw [hk]
        simp [upsert, List.map_cons, List.sum_cons]
        omega
      · have hfound' : lookupCounters rest id = some t := by
          simpa [lookupCounters, hk] using hfound
        have hrec := ih hfound'
        simp [upsert, hk, List.map_cons, List.sum_cons]
        omega

/-- Appending an entry does not increase a sum of contributions, when the new entry
contributes at most 0. -/
private theorem sum_map_upsert_le_of_absent (f : TopicId × TopicCounters → Int)
    (l : List (TopicId × TopicCounters)) (id : TopicId) (u : TopicCounters)
    (habsent : lookupCounters l id = none) (hle : f (id, u) ≤ 0) :
    ((upsert l id u).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simpa [upsert] using hle
  | cons head rest ih =>
      obtain ⟨k, v⟩ := head
      by_cases hk : k = id
      · simp [lookupCounters, hk] at habsent
      · have habsent' : lookupCounters rest id = none := by
          simpa [lookupCounters, hk] using habsent
        have hrec := ih habsent'
        simp [upsert, hk, List.map_cons, List.sum_cons]
        omega

/-! ## Sign facts -/

/-- The `P1` term is at or above 0. -/
theorem p1Term_nonneg {tp : TopicParams} (h : TopicParams.Valid tp)
    (now : Millis) (t : TopicCounters) :
    0 ≤ tp.timeInMeshWeight * (p1 tp now t : Int) :=
  Int.mul_nonneg h.timeInMeshWeight_nonneg (Int.natCast_nonneg _)

/-- The `P2` term is at or above 0. -/
theorem p2Term_nonneg {tp : TopicParams} (h : TopicParams.Valid tp)
    (t : TopicCounters) :
    0 ≤ tp.firstMessageDeliveriesWeight * (t.firstMessageDeliveries : Int) :=
  Int.mul_nonneg h.firstMessageDeliveriesWeight_nonneg (Int.natCast_nonneg _)

/-- The `P3` term is at or below 0. -/
theorem p3Term_nonpos {tp : TopicParams} (h : TopicParams.Valid tp)
    (now : Millis) (t : TopicCounters) :
    tp.meshMessageDeliveriesWeight * (p3 tp now t : Int) ≤ 0 :=
  Int.mul_nonpos_of_nonpos_of_nonneg h.meshMessageDeliveriesWeight_nonpos
    (Int.natCast_nonneg _)

/-- The `P3b` term is at or below 0. -/
theorem p3bTerm_nonpos {tp : TopicParams} (h : TopicParams.Valid tp)
    (t : TopicCounters) :
    tp.meshFailurePenaltyWeight * (t.meshFailurePenalty : Int) ≤ 0 :=
  Int.mul_nonpos_of_nonpos_of_nonneg h.meshFailurePenaltyWeight_nonpos
    (Int.natCast_nonneg _)

/-- The `P4` term is at or below 0. -/
theorem p4Term_nonpos {tp : TopicParams} (h : TopicParams.Valid tp)
    (t : TopicCounters) :
    tp.invalidMessageDeliveriesWeight * (p4 t : Int) ≤ 0 :=
  Int.mul_nonpos_of_nonpos_of_nonneg h.invalidMessageDeliveriesWeight_nonpos
    (Int.natCast_nonneg _)

/-- The `P6` term is at or below 0. -/
theorem p6Term_nonpos {g : GlobalParams} (h : GlobalParams.Valid g) (s : PeerState) :
    g.ipColocationFactorWeight * (p6 g s : Int) ≤ 0 :=
  Int.mul_nonpos_of_nonpos_of_nonneg h.ipColocationFactorWeight_nonpos
    (Int.natCast_nonneg _)

/-- The `P7` term is at or below 0. -/
theorem p7Term_nonpos {g : GlobalParams} (h : GlobalParams.Valid g) (s : PeerState) :
    g.behaviourPenaltyWeight * (p7 g s : Int) ≤ 0 :=
  Int.mul_nonpos_of_nonpos_of_nonneg h.behaviourPenaltyWeight_nonpos
    (Int.natCast_nonneg _)

/-! ## The topic cap -/

/-- The topic part never exceeds a positive topic score cap. The statement needs no
`Params.Valid`: the cap holds for any parameters. -/
theorem topicPart_le_cap (p : Params) (now : Millis) (s : PeerState)
    (hcap : 0 < p.global.topicScoreCap) :
    topicPart p now s ≤ p.global.topicScoreCap := by
  dsimp only [topicPart]
  split <;> omega

/-! ## Decay theorems -/

/-- A decay step never increases a counter, when the decay factor is at most `scoreScale`. -/
theorem decayCounter_le (d : Nat) (z : Nat) (c : Nat) (hd : d ≤ scoreScale) :
    decayCounter d z c ≤ c := by
  have hdiv : c * d / scoreScale ≤ c := by
    exact Nat.div_le_of_le_mul (by
      rw [Nat.mul_comm scoreScale c]
      exact Nat.mul_le_mul_left c hd)
  unfold decayCounter
  split <;> omega

/-- A counter below `decayToZero` becomes 0 after a decay step, when the decay factor is at most
`scoreScale`. -/
theorem decayCounter_of_lt (d : Nat) (z : Nat) (c : Nat) (hd : d ≤ scoreScale)
    (hc : c < z) :
    decayCounter d z c = 0 := by
  have hdiv : c * d / scoreScale ≤ c := by
    exact Nat.div_le_of_le_mul (by
      rw [Nat.mul_comm scoreScale c]
      exact Nat.mul_le_mul_left c hd)
  unfold decayCounter
  split
  · rfl
  · omega

/-- The behavior penalty never increases under a decay step. -/
theorem decay_behaviourPenalty_le {p : Params} (h : Params.Valid p) (s : PeerState) :
    (decay p s).behaviourPenalty ≤ s.behaviourPenalty := by
  simpa [decay] using
    decayCounter_le p.global.behaviourPenaltyDecay p.global.decayToZero
      s.behaviourPenalty h.global.behaviourPenaltyDecay_le

/-- A decay step leaves the mesh time, the graft time, and the mesh membership unchanged. -/
theorem decay_preserves_mesh {p : Params} (s : PeerState) (id : TopicId) :
    (countersOf (decay p s) id).timeInMesh = (countersOf s id).timeInMesh ∧
    (countersOf (decay p s) id).graftTime = (countersOf s id).graftTime ∧
    (countersOf (decay p s) id).inMesh = (countersOf s id).inMesh := by
  rw [countersOf_decay]
  cases hlook : lookupCounters s.topics id with
  | none => simp [countersOf, hlook, TopicCounters.zero]
  | some t =>
      simp only [countersOf, hlook]
      cases hcfg : p.topics id with
      | none => simp [decayEntry, hcfg]
      | some tp => simp [decayEntry, decayTopic, hcfg]

/-- The `P2` counter never increases under a decay step. -/
theorem decay_firstMessageDeliveries_le {p : Params} (h : Params.Valid p)
    (s : PeerState) (id : TopicId) :
    (countersOf (decay p s) id).firstMessageDeliveries ≤
      (countersOf s id).firstMessageDeliveries := by
  rw [countersOf_decay]
  cases hlook : lookupCounters s.topics id with
  | none => simp [countersOf, hlook, TopicCounters.zero]
  | some t =>
      simp only [countersOf, hlook]
      cases hcfg : p.topics id with
      | none => simp [decayEntry, hcfg]
      | some tp =>
          simp only [decayEntry, hcfg]
          exact decayCounter_le tp.firstMessageDeliveriesDecay p.global.decayToZero
            t.firstMessageDeliveries (h.topic id tp hcfg).firstMessageDeliveriesDecay_le

/-- The `P3` counter never increases under a decay step. -/
theorem decay_meshMessageDeliveries_le {p : Params} (h : Params.Valid p)
    (s : PeerState) (id : TopicId) :
    (countersOf (decay p s) id).meshMessageDeliveries ≤
      (countersOf s id).meshMessageDeliveries := by
  rw [countersOf_decay]
  cases hlook : lookupCounters s.topics id with
  | none => simp [countersOf, hlook, TopicCounters.zero]
  | some t =>
      simp only [countersOf, hlook]
      cases hcfg : p.topics id with
      | none => simp [decayEntry, hcfg]
      | some tp =>
          simp only [decayEntry, hcfg]
          exact decayCounter_le tp.meshMessageDeliveriesDecay p.global.decayToZero
            t.meshMessageDeliveries (h.topic id tp hcfg).meshMessageDeliveriesDecay_le

/-- The `P3b` counter never increases under a decay step. -/
theorem decay_meshFailurePenalty_le {p : Params} (h : Params.Valid p)
    (s : PeerState) (id : TopicId) :
    (countersOf (decay p s) id).meshFailurePenalty ≤
      (countersOf s id).meshFailurePenalty := by
  rw [countersOf_decay]
  cases hlook : lookupCounters s.topics id with
  | none => simp [countersOf, hlook, TopicCounters.zero]
  | some t =>
      simp only [countersOf, hlook]
      cases hcfg : p.topics id with
      | none => simp [decayEntry, hcfg]
      | some tp =>
          simp only [decayEntry, hcfg]
          exact decayCounter_le tp.meshFailurePenaltyDecay p.global.decayToZero
            t.meshFailurePenalty (h.topic id tp hcfg).meshFailurePenaltyDecay_le

/-- The `P4` counter never increases under a decay step. -/
theorem decay_invalidMessageDeliveries_le {p : Params} (h : Params.Valid p)
    (s : PeerState) (id : TopicId) :
    (countersOf (decay p s) id).invalidMessageDeliveries ≤
      (countersOf s id).invalidMessageDeliveries := by
  rw [countersOf_decay]
  cases hlook : lookupCounters s.topics id with
  | none => simp [countersOf, hlook, TopicCounters.zero]
  | some t =>
      simp only [countersOf, hlook]
      cases hcfg : p.topics id with
      | none => simp [decayEntry, hcfg]
      | some tp =>
          simp only [decayEntry, hcfg]
          exact decayCounter_le tp.invalidMessageDeliveriesDecay p.global.decayToZero
            t.invalidMessageDeliveries (h.topic id tp hcfg).invalidMessageDeliveriesDecay_le

/-- The first message delivery counter stays at or below its cap. The topic must be
configured. -/
theorem firstDelivery_le_cap {p : Params} {s : PeerState} {id : TopicId} {tp : TopicParams}
    (hcfg : p.topics id = some tp) :
    (countersOf (firstDelivery p s id) id).firstMessageDeliveries ≤
      tp.firstMessageDeliveriesCap := by
  have h : min ((countersOf s id).firstMessageDeliveries + 1)
      tp.firstMessageDeliveriesCap ≤ tp.firstMessageDeliveriesCap :=
    Nat.min_le_right _ _
  simpa [firstDelivery, hcfg, setCounters, countersOf, lookupCounters_upsert_same] using h

/-- The mesh message delivery counter stays at or below its cap. The topic must be
configured. -/
theorem meshDelivery_le_cap {p : Params} {s : PeerState} {id : TopicId} {tp : TopicParams}
    (hcfg : p.topics id = some tp) :
    (countersOf (meshDelivery p s id) id).meshMessageDeliveries ≤
      tp.meshMessageDeliveriesCap := by
  have h : min ((countersOf s id).meshMessageDeliveries + 1)
      tp.meshMessageDeliveriesCap ≤ tp.meshMessageDeliveriesCap :=
    Nat.min_le_right _ _
  simpa [meshDelivery, hcfg, setCounters, countersOf, lookupCounters_upsert_same] using h

/-! ## Invalid delivery monotonicity -/

/-- One invalid delivery leaves `P1` unchanged. -/
private theorem p1_invalidStep (tp : TopicParams) (now : Millis) (t : TopicCounters) :
    p1 tp now (invalidStep t) = p1 tp now t := rfl

/-- One invalid delivery leaves `P3` unchanged. -/
private theorem p3_invalidStep (tp : TopicParams) (now : Millis) (t : TopicCounters) :
    p3 tp now (invalidStep t) = p3 tp now t := rfl

/-- The `P4` square does not fall when the counter grows. -/
private theorem p4_invalidStep_mono (t : TopicCounters) :
    p4 t ≤ p4 (invalidStep t) :=
  Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)

/-- One invalid delivery does not raise the topic score, when the `P4` weight is at or below
0. -/
private theorem topicScore_invalidStep_le (tp : TopicParams) (now : Millis)
    (t : TopicCounters) (hw : tp.invalidMessageDeliveriesWeight ≤ 0) :
    topicScore tp now (invalidStep t) ≤ topicScore tp now t := by
  have h1 := p1_invalidStep tp now t
  have h3 := p3_invalidStep tp now t
  have hp4 : (p4 t : Int) ≤ (p4 (invalidStep t) : Int) :=
    Int.ofNat_le.mpr (p4_invalidStep_mono t)
  have hprod := Int.mul_le_mul_of_nonpos_left hw hp4
  unfold topicScore
  have h2 : (invalidStep t).firstMessageDeliveries = t.firstMessageDeliveries := rfl
  have h4 : (invalidStep t).meshFailurePenalty = t.meshFailurePenalty := rfl
  rw [h1, h3, h2, h4]
  omega

/-- One invalid delivery does not raise a topic contribution, when the topic weight is at or
above 0 and the `P4` weight is at or below 0. -/
private theorem topicContribution_invalidStep_le (p : Params) (now : Millis)
    (id : TopicId) {tp : TopicParams} (htp : p.topics id = some tp)
    (hW : 0 ≤ tp.topicWeight) (hw : tp.invalidMessageDeliveriesWeight ≤ 0)
    (t : TopicCounters) :
    topicContribution p now (id, invalidStep t) ≤ topicContribution p now (id, t) := by
  have hts := topicScore_invalidStep_le tp now t hw
  have hmul : tp.topicWeight * topicScore tp now (invalidStep t) ≤
      tp.topicWeight * topicScore tp now t :=
    Int.mul_le_mul_of_nonneg_left hts hW
  have hdiv := Int.tdiv_le_tdiv
    (by decide : (0 : Int) < (scoreScale : Int)) hmul
  simpa [topicContribution, htp] using hdiv

/-- The contribution of a fresh counters value after one invalid delivery is at or below 0,
when the topic weight is at or above 0 and the `P4` weight is at or below 0. -/
private theorem topicContribution_invalidStep_zero_nonpos (p : Params) (now : Millis)
    (id : TopicId) {tp : TopicParams} (htp : p.topics id = some tp)
    (hW : 0 ≤ tp.topicWeight) (hw : tp.invalidMessageDeliveriesWeight ≤ 0) :
    topicContribution p now (id, invalidStep TopicCounters.zero) ≤ 0 := by
  have hts : topicScore tp now (invalidStep TopicCounters.zero) =
      tp.invalidMessageDeliveriesWeight := by
    simp [topicScore, p1, p3, p4, elapsed, invalidStep, TopicCounters.zero]
  have hmul : tp.topicWeight * tp.invalidMessageDeliveriesWeight ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos hW hw
  have hdiv : (tp.topicWeight * tp.invalidMessageDeliveriesWeight).tdiv
      (scoreScale : Int) ≤ 0 := by
    have h0 : (0 : Int).tdiv (scoreScale : Int) = 0 := by decide
    have := Int.tdiv_le_tdiv (by decide : (0 : Int) < (scoreScale : Int)) hmul
    omega
  simpa [topicContribution, htp, hts] using hdiv

/-- The topic cap preserves the order of the raw topic part. -/
private theorem topicPart_mono {p : Params} {now : Millis} {s s' : PeerState}
    (h : rawTopicPart p now s' ≤ rawTopicPart p now s) :
    topicPart p now s' ≤ topicPart p now s := by
  dsimp only [topicPart]
  split <;> split <;> omega

/-- The score preserves the order of the topic part, when the three global inputs are equal. -/
private theorem score_le_of_topicPart_le {p : Params} {now : Millis} {s s' : PeerState}
    (h : topicPart p now s' ≤ topicPart p now s)
    (happ : s'.appScore = s.appScore)
    (hip : s'.ipColocation = s.ipColocation)
    (hbp : s'.behaviourPenalty = s.behaviourPenalty) :
    score p s' now ≤ score p s now := by
  have happ' : p.global.appSpecificWeight * s'.appScore =
      p.global.appSpecificWeight * s.appScore := by
    rw [happ]
  have hp6 : p6 p.global s' = p6 p.global s := by
    unfold p6
    rw [hip]
  have hp7 : p7 p.global s' = p7 p.global s := by
    unfold p7
    rw [hbp]
  unfold score
  rw [happ', hp6, hp7]
  exact Int.add_le_add_right (Int.add_le_add_right (Int.add_le_add_right h _) _) _

/-- One more invalid delivery never raises the score of a peer. The proof consumes the topic
weight sign and the `P4` weight sign of the target topic. The other topics do not move. -/
theorem invalidDelivery_score_mono {p : Params} (h : Params.Valid p)
    (now : Millis) (s : PeerState) (id : TopicId) :
    score p (invalidDelivery p s id) now ≤ score p s now := by
  cases hcfg : p.topics id with
  | none => simp [invalidDelivery, hcfg]
  | some tp =>
      simp only [invalidDelivery, hcfg]
      have htp := h.topic id tp hcfg
      have hraw :
          rawTopicPart p now
            (setCounters s id (invalidStep (countersOf s id))) ≤
          rawTopicPart p now s := by
        cases hlook : lookupCounters s.topics id with
        | none =>
            have hu : countersOf s id = TopicCounters.zero := by
              simp [countersOf, hlook]
            rw [hu]
            exact sum_map_upsert_le_of_absent (topicContribution p now) s.topics id
              (invalidStep TopicCounters.zero) hlook
              (topicContribution_invalidStep_zero_nonpos p now id hcfg
                htp.topicWeight_nonneg htp.invalidMessageDeliveriesWeight_nonpos)
        | some t =>
            have hu : countersOf s id = t := by
              simp [countersOf, hlook]
            rw [hu]
            exact sum_map_upsert_le_of_found (topicContribution p now) s.topics id
              (invalidStep t) t hlook
              (topicContribution_invalidStep_le p now id hcfg
                htp.topicWeight_nonneg htp.invalidMessageDeliveriesWeight_nonpos t)
      have hpart := topicPart_mono hraw
      have happ : (setCounters s id (invalidStep (countersOf s id))).appScore =
          s.appScore := rfl
      have hip : (setCounters s id (invalidStep (countersOf s id))).ipColocation =
          s.ipColocation := rfl
      have hbp : (setCounters s id (invalidStep (countersOf s id))).behaviourPenalty =
          s.behaviourPenalty := rfl
      exact score_le_of_topicPart_le hpart happ hip hbp

/-- An invalid delivery to a topic with no configured parameters leaves the score
unchanged. -/
theorem invalidDelivery_unconfigured_score {p : Params} {s : PeerState} {id : TopicId}
    (hcfg : p.topics id = none) (now : Millis) :
    score p (invalidDelivery p s id) now = score p s now := by
  simp [invalidDelivery, hcfg]

/-! ## The fresh peer -/

/-- The raw topic part of a fresh peer is 0. -/
private theorem rawTopicPart_zero (p : Params) (now : Millis) :
    rawTopicPart p now PeerState.zero = 0 := rfl

/-- The topic part of a fresh peer is 0, for any parameters. -/
private theorem topicPart_zero (p : Params) (now : Millis) :
    topicPart p now PeerState.zero = 0 := by
  have hraw := rawTopicPart_zero p now
  dsimp only [topicPart]
  rw [hraw]
  split <;> omega

/-- A fresh peer scores 0. The statement needs no `Params.Valid`: it holds for any
parameters. -/
theorem freshPeer_scores_zero (p : Params) (now : Millis) :
    score p PeerState.zero now = 0 := by
  have hpart := topicPart_zero p now
  unfold score
  rw [hpart]
  simp [p6, p7, PeerState.zero]

/-! ## Prune -/

/-- A prune with an active delivery deficit adds the square of the deficit to the failure
penalty. The peer is in the mesh, the topic is configured, the activation window has passed,
and the delivery count is below the threshold. -/
theorem prune_adds_deficit {p : Params} {s : PeerState} {now : Millis} {id : TopicId}
    {tp : TopicParams} {t : TopicCounters}
    (hcfg : p.topics id = some tp) (ht : countersOf s id = t) (hin : t.inMesh)
    (hact : tp.meshMessageDeliveriesActivation < elapsed now t)
    (hdef : t.meshMessageDeliveries < tp.meshMessageDeliveriesThreshold) :
    (countersOf (prune p s now id) id).meshFailurePenalty =
      t.meshFailurePenalty +
        (tp.meshMessageDeliveriesThreshold - t.meshMessageDeliveries) *
          (tp.meshMessageDeliveriesThreshold - t.meshMessageDeliveries) := by
  have hprune : prune p s now id = setCounters s id (pruneCounters p now id t) := by
    simp [prune, ht, hin]
  rw [hprune]
  simp [setCounters, countersOf, lookupCounters_upsert_same, pruneCounters, hcfg, hact, hdef]

/-- A prune with no active delivery deficit leaves the failure penalty unchanged. -/
theorem prune_without_deficit_keeps_penalty {p : Params} {s : PeerState} {now : Millis}
    {id : TopicId} {tp : TopicParams} {t : TopicCounters}
    (hcfg : p.topics id = some tp) (ht : countersOf s id = t) (hin : t.inMesh)
    (hno : ¬ (tp.meshMessageDeliveriesActivation < elapsed now t ∧
      t.meshMessageDeliveries < tp.meshMessageDeliveriesThreshold)) :
    (countersOf (prune p s now id) id).meshFailurePenalty = t.meshFailurePenalty := by
  have hprune : prune p s now id = setCounters s id (pruneCounters p now id t) := by
    simp [prune, ht, hin]
  rw [hprune]
  simp [setCounters, countersOf, lookupCounters_upsert_same, pruneCounters, hcfg, hno]

/-- A prune removes a peer from the mesh. The statement needs no parameter hypothesis. -/
theorem prune_leaves_mesh {p : Params} {s : PeerState} {now : Millis} {id : TopicId}
    {t : TopicCounters} (ht : countersOf s id = t) (hin : t.inMesh) :
    ¬ (countersOf (prune p s now id) id).inMesh := by
  have hprune : prune p s now id = setCounters s id (pruneCounters p now id t) := by
    simp [prune, ht, hin]
  rw [hprune]
  simp [setCounters, countersOf, lookupCounters_upsert_same]
  cases hcfg : p.topics id with
  | none => simp [pruneCounters, hcfg]
  | some tp =>
      simp [pruneCounters, hcfg]
      split <;> simp

end Libp2p.Protocols.Gossipsub.Score
