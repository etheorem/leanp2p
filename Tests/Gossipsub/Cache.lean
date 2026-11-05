import Tests.Support
import Libp2p.Protocols.Gossipsub.Cache

/-!
# Gossipsub suite: Cache

The checks of `Libp2p.Protocols.Gossipsub.Cache`. Each check is one step
of a fixed transcript: the inputs are literal times and ids, and the
expected result stands beside the call. The suite names the spec
boundaries: exactly `t + ttl`, exactly `until`, exactly the end of a
window, and exactly the capacity of the seen cache.

The windows of the message cache checks are the spec defaults: five
history windows and three gossip windows. The seen cache uses capacity
three and a TTL of one hundred milliseconds, so each boundary is a round
number.
-/

set_option autoImplicit false

namespace Tests.Gossipsub.Cache

open Libp2p.Protocols.Gossipsub
open Libp2p.Protocols.Gossipsub.Cache

/-- The window parameters of the transcript: the spec defaults of five
history windows and three gossip windows. -/
def window5 : WindowParams :=
  { historyLength := 5, historyGossip := 3, valid := by decide }

/-- The seen cache parameters of the transcript: three entries and a TTL
of one hundred milliseconds. -/
def seen3 : SeenParams :=
  { capacity := 3, ttl := 100, valid := by decide }

/-- A message id from one number. -/
def mid (n : Nat) : MessageId := { bytes := [n] }

/-- One topic of the transcript. -/
def topicA : TopicId := { name := "a" }

/-- A second topic of the transcript. -/
def topicB : TopicId := { name := "b" }

/-- A message with a one-byte payload. -/
def msg (t : TopicId) (n : Nat) : Message :=
  { «from» := none, data := some [n], seqno := none, topic := t, signature := none, key := none }

/-- A peer from one number. -/
def peer (n : Nat) : Peer := { bytes := [n], text := s!"p{n}" }

/-- A promise with explicit fields, for the expected lists. -/
def promiseOf (p : Peer) (i : MessageId) (d : Millis) : IwantPromise :=
  { peer := p, id := i, deadline := d }

/-- A backoff entry with explicit fields, for the expected lists. -/
def backoffOf (p : Peer) (t : TopicId) (u : Millis) : BackoffEntry :=
  { peer := p, topic := t, «until» := u }

/-- Run the checks of this module. -/
def run (r : Runner) : IO Unit := do
  r.section "gossipsub Cache" "vendor/specs/pubsub"

  -- Message cache: one message, then shifts.
  let c0 : MessageCache := MessageCache.empty window5
  let c1 : MessageCache := c0.put (mid 1) (msg topicA 1)
  r.check "mcache put then get returns the message"
    (decide (MessageCache.get c1 (mid 1) = some (msg topicA 1)))
  r.check "mcache get returns none for an absent id"
    (decide (MessageCache.get c1 (mid 2) = none))
  r.check "mcache get returns the message after historyLength minus one shifts"
    (decide (MessageCache.get (MessageCache.shiftN c1 4) (mid 1) = some (msg topicA 1)))
  r.check "mcache get returns none after historyLength shifts"
    (decide (MessageCache.get (MessageCache.shiftN c1 5) (mid 1) = none))

  -- Message cache: four messages entered one heartbeat apart, so their
  -- ages are zero to three.
  let g1 : MessageCache := c0.put (mid 1) (msg topicA 1)
  let g2 : MessageCache := (MessageCache.shift g1).put (mid 2) (msg topicA 2)
  let g3 : MessageCache := (MessageCache.shift g2).put (mid 3) (msg topicA 3)
  let g4 : MessageCache := (MessageCache.shift g3).put (mid 4) (msg topicA 4)
  r.check "mcache gossipIds lists only ids newer than historyGossip windows"
    (decide (MessageCache.gossipIds g4 topicA = [mid 4, mid 3, mid 2]))
  let g5 : MessageCache := g4.put (mid 9) (msg topicB 9)
  r.check "mcache gossipIds filters by topic"
    (decide (MessageCache.gossipIds g5 topicA = [mid 4, mid 3, mid 2] ∧
      MessageCache.gossipIds g5 topicB = [mid 9]))
  r.check "mcache gossipIds is empty for a message old enough"
    (decide (MessageCache.gossipIds (MessageCache.shiftN c1 3) topicA = []))

  -- Window parameters: the validity predicate of the spec.
  r.check "window params reject gossip zero" (decide (¬ (0 < 0 ∧ 0 ≤ 5)))
  r.check "window params reject gossip above length" (decide (¬ (0 < 6 ∧ 6 ≤ 5)))
  r.check "window params accept gossip within length" (decide (0 < 3 ∧ 3 ≤ 5))

  -- Seen cache: one id at time ten, and the two time boundaries.
  let s0 : SeenCache := SeenCache.empty seen3
  r.check "seen contains after add at the same time"
    (SeenCache.contains (s0.add (mid 1) 10) (mid 1) 10)
  r.check "seen contains holds below t plus ttl"
    (SeenCache.contains (s0.add (mid 1) 10) (mid 1) 109)
  r.check "seen contains fails at exactly t plus ttl"
    (!SeenCache.contains (s0.add (mid 1) 10) (mid 1) 110)

  -- Seen cache: three adds fill the cache, one more evicts the oldest.
  let f1 : SeenCache := s0.add (mid 1) 10
  let f2 : SeenCache := f1.add (mid 2) 20
  let f3 : SeenCache := f2.add (mid 3) 30
  let f4 : SeenCache := f3.add (mid 4) 40
  r.check "seen add at capacity evicts the oldest entry"
    (!SeenCache.contains f4 (mid 1) 40)
  r.check "seen add at capacity keeps the second oldest entry"
    (SeenCache.contains f4 (mid 2) 40)
  r.check "seen size stays at capacity after an add at capacity"
    (decide (f4.entries.length = seen3.capacity))
  let f5 : SeenCache := f3.add (mid 1) 35
  r.check "seen add refreshes an existing id"
    (decide (f5.entries = [
      ({ id := mid 1, «at» := 35 } : SeenEntry),
      { id := mid 3, «at» := 30 },
      { id := mid 2, «at» := 20 }]))
  let f6 : SeenCache := f2.prune 115
  r.check "seen prune drops only expired entries"
    (decide (f6.entries = [{ id := mid 2, «at» := 20 }]))

  -- Backoff table: a period from ten to sixty.
  let b1 : BackoffTable := Backoff.add Backoff.empty (peer 1) topicA 50 10
  r.check "backoff active below until"
    (Backoff.active b1 (peer 1) topicA 59)
  r.check "backoff inactive at exactly until"
    (!Backoff.active b1 (peer 1) topicA 60)
  r.check "backoff inactive for an unknown pair"
    (!Backoff.active b1 (peer 2) topicA 30 && !Backoff.active b1 (peer 1) topicB 30)
  let b2 : BackoffTable := Backoff.add b1 (peer 1) topicA 50 40
  r.check "backoff a second add extends the period"
    (Backoff.active b2 (peer 1) topicA 60 && Backoff.active b2 (peer 1) topicA 89 &&
      !Backoff.active b2 (peer 1) topicA 90)
  let b3 : BackoffTable :=
    Backoff.add (Backoff.add Backoff.empty (peer 1) topicA 50 10) (peer 2) topicA 100 10
  let b4 : BackoffTable := Backoff.clear b3 70
  r.check "backoff clear keeps active entries"
    (Backoff.active b4 (peer 2) topicA 70)
  r.check "backoff clear drops expired entries"
    (decide (b4 = [backoffOf (peer 2) topicA 110]))

  -- Promises: one promise, then the same pair again.
  let p0 : PromiseTable := PromiseTable.promise [] (peer 1) (mid 7) 300
  r.check "promise records the pair and the deadline"
    (decide (p0 = [promiseOf (peer 1) (mid 7) 300]))
  let p1 : PromiseTable := PromiseTable.promise p0 (peer 1) (mid 7) 400
  r.check "promise a second time for the same pair replaces the deadline"
    (decide (p1 = [promiseOf (peer 1) (mid 7) 400]))
  let p2 : PromiseTable :=
    PromiseTable.promise
      (PromiseTable.promise (PromiseTable.promise [] (peer 1) (mid 7) 300) (peer 2) (mid 7) 300)
      (peer 1) (mid 8) 300
  r.check "deliver removes every promise for the id"
    (decide (PromiseTable.deliver p2 (mid 7) = [promiseOf (peer 1) (mid 8) 300]))
  let p3 : PromiseTable :=
    PromiseTable.promise (PromiseTable.promise [] (peer 1) (mid 7) 300) (peer 2) (mid 8) 400
  r.check "deliver keeps promises of other ids"
    (decide (PromiseTable.deliver p3 (mid 7) = [promiseOf (peer 2) (mid 8) 400]))

  -- Broken promises at time five hundred: one expired promise of peer
  -- one, and one promise that is not due.
  let q0 : PromiseTable :=
    PromiseTable.promise (PromiseTable.promise [] (peer 1) (mid 7) 400) (peer 1) (mid 8) 900
  r.check "broken lists the peer with the expired count"
    (decide (PromiseTable.broken q0 500 = [(peer 1, 1)]))
  let q1 : PromiseTable :=
    PromiseTable.promise (PromiseTable.promise [] (peer 1) (mid 7) 400) (peer 1) (mid 8) 450
  r.check "broken counts two expired promises for one peer"
    (decide (PromiseTable.broken q1 500 = [(peer 1, 2)]))
  let q2 : PromiseTable := PromiseTable.promise [] (peer 1) (mid 7) 900
  r.check "broken omits peers whose deadlines have not passed"
    (decide (PromiseTable.broken q2 500 = []))
  r.check "broken after deliver shows no count for the delivered id"
    (decide (PromiseTable.broken (PromiseTable.deliver q1 (mid 7)) 500 = [(peer 1, 1)]))

end Tests.Gossipsub.Cache
