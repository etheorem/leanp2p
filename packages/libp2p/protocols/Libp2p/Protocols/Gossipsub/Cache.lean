import Libp2p.Protocols.Gossipsub.Types

/-!
# Gossipsub caches

The four tables of the gossipsub router: the message cache, the seen
cache, the backoff table, and the in-flight IWANT promises.

The tables are pure data. Time is an input (`Millis`), never a clock, so
the router core drives them from a `step` and the suite drives them with
fixed times.

Every table is a plain `List`, newest first. An add prepends. The spec
describes the message cache as a ring of history windows; this module
stores one flat list instead and carries each entry's age, which states
the same bound (`age < historyLength`) and makes each theorem one list
induction.

The message cache and the seen cache are models. The router runs a
keyed index for each (`MessageIndex`, `SeenIndex`), because each list
operation walks every entry. A property test pins each index to its
model.

The spec sections are `vendor/specs/pubsub/gossipsub/gossipsub-v1.0.md`
("Message Cache", and the `seen` cache paragraph) and
`vendor/specs/pubsub/gossipsub/gossipsub-v1.1.md` ("Prune Backoff and
Peer Exchange", and "Spam Protection Measures").

The cache takes its parameters as arguments. It reads no default from
`Constants.lean`, so the router core owns the spec defaults.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Cache

/-! ## Message cache

The message cache keeps the newest `historyLength` heartbeats. A `put`
enters the current window with age zero. A `shift` ages every entry by
one heartbeat and drops the entries that reach `historyLength`. Gossip
lists the ids from the newest `historyGossip` windows of one topic.
-/

/-- The window counts of the message cache. `historyLength` is the spec
`mcache_len` (default 5), the number of heartbeats the cache holds.
`historyGossip` is the spec `mcache_gossip` (default 3), the number of
newest heartbeats that gossip lists. The `valid` field carries the spec
bound, so no cache can gossip zero windows or gossip more windows than it
stores. -/
structure WindowParams where
  /-- The number of heartbeats the cache keeps. -/
  historyLength : Nat
  /-- The number of newest heartbeats that gossip lists. -/
  historyGossip : Nat
  /-- The spec bound `0 < historyGossip` and
  `historyGossip ≤ historyLength`. -/
  valid : 0 < historyGossip ∧ historyGossip ≤ historyLength
  deriving Repr

/-- One cached message. `age` counts the heartbeats since the `put`, so
age zero is the current window. The `topic` copies the required topic
field of the message, so `gossipIds` filters a topic without unpacking
the message. -/
structure Cached where
  /-- The message id, computed by the caller. -/
  id : MessageId
  /-- The topic of the message. -/
  topic : TopicId
  /-- The message itself. -/
  message : Message
  /-- The number of heartbeats since the `put`. -/
  age : Nat
  deriving DecidableEq, Repr

/-- The message cache: the window parameters and the entries, newest
first. -/
structure MessageCache where
  /-- The window counts. -/
  params : WindowParams
  /-- The cached messages, newest first. -/
  entries : List Cached
  deriving Repr

/-- An empty cache with the given parameters. -/
def MessageCache.empty (p : WindowParams) : MessageCache :=
  { params := p, entries := [] }

/-- Add a message to the current window. The id is an argument, because
the message id function lives in the signing policy and this module must
not import it. The entry takes age zero, the current window. -/
def MessageCache.put (c : MessageCache) (id : MessageId) (m : Message) : MessageCache :=
  { c with
    entries := { id := id, topic := m.topic, message := m, age := 0 } :: c.entries }

/-- The message with the given id, if the cache holds it. The search runs
newest first, so a re-`put` id finds its newest message. -/
def MessageCache.get (c : MessageCache) (id : MessageId) : Option Message :=
  (c.entries.find? (fun e => decide (e.id = id))).map (fun e => e.message)

/-- Shift one heartbeat. Every entry ages by one, and an entry whose new
age reaches `historyLength` leaves the cache. -/
def MessageCache.shift (c : MessageCache) : MessageCache :=
  { c with
    entries :=
      c.entries.filterMap (fun e =>
        if e.age + 1 < c.params.historyLength then some { e with age := e.age + 1 } else none) }

/-- Shift `k` heartbeats. This is the iteration form that the lifetime
theorems state, because the `^[ ]` notation is not part of the core
library. -/
def MessageCache.shiftN (c : MessageCache) : Nat → MessageCache
  | 0 => c
  | k + 1 => (MessageCache.shiftN c k).shift

/-- The ids that gossip lists for a topic: the entries of that topic whose
age is below `historyGossip`, newest first. -/
def MessageCache.gossipIds (c : MessageCache) (topic : TopicId) : List MessageId :=
  (c.entries.filter (fun e => decide (e.topic = topic ∧ e.age < c.params.historyGossip))).map
    (fun e => e.id)

/-- The window bound: every entry is younger than `historyLength`
heartbeats. This is the spec bound "at most `history_length` windows" in
the flat-list form. -/
def MessageCache.windowInvariant (c : MessageCache) : Prop :=
  ∀ e ∈ c.entries, e.age < c.params.historyLength

/-- The window bound implies a positive length. -/
theorem historyLength_pos (p : WindowParams) : 0 < p.historyLength :=
  Nat.lt_of_lt_of_le p.valid.1 p.valid.2

/-- A `put` is found by `get` at its own id. -/
theorem put_get (c : MessageCache) (id : MessageId) (m : Message) :
    MessageCache.get (MessageCache.put c id m) id = some m := by
  simp [MessageCache.get, MessageCache.put]

private theorem shiftN_zero (c : MessageCache) : MessageCache.shiftN c 0 = c := rfl

private theorem shiftN_succ (c : MessageCache) (k : Nat) :
    MessageCache.shiftN c (k + 1) = (MessageCache.shiftN c k).shift := rfl

private theorem shift_params (c : MessageCache) : (MessageCache.shift c).params = c.params :=
  rfl

private theorem shiftN_params (c : MessageCache) (k : Nat) :
    (MessageCache.shiftN c k).params = c.params := by
  induction k with
  | zero => rw [shiftN_zero c]
  | succ k ih => rw [shiftN_succ, shift_params, ih]

/-- Every entry of a shifted cache is an input entry with age one higher,
and that higher age is still below `historyLength`. -/
private theorem mem_shift_entries {c : MessageCache} {e' : Cached}
    (h : e' ∈ (MessageCache.shift c).entries) :
    ∃ e ∈ c.entries,
      e' = { e with age := e.age + 1 } ∧ e.age + 1 < c.params.historyLength := by
  simp only [MessageCache.shift, List.mem_filterMap] at h
  obtain ⟨e, he, hf⟩ := h
  split at hf
  · rename_i hlt
    rw [Option.some.injEq] at hf
    exact ⟨e, he, hf.symm, hlt⟩
  · simp at hf

private theorem shift_age_lt {c : MessageCache} {e : Cached}
    (h : e ∈ (MessageCache.shift c).entries) : e.age < c.params.historyLength := by
  obtain ⟨e0, _, hEq, hlt⟩ := mem_shift_entries h
  rw [hEq]
  exact hlt

/-- After `k` shifts every entry is at least `k` heartbeats old. -/
private theorem shiftN_age_ge (c : MessageCache) (k : Nat) :
    ∀ e ∈ (MessageCache.shiftN c k).entries, k ≤ e.age := by
  induction k with
  | zero =>
    intro e _
    omega
  | succ k ih =>
    intro e he
    rw [shiftN_succ] at he
    obtain ⟨e0, he0, hEq, _⟩ := mem_shift_entries he
    rw [hEq]
    have hge := ih e0 he0
    show k + 1 ≤ e0.age + 1
    omega

/-- The entries of a shifted cache whose head survives: the head moves to
age one, and the tail shifts as usual. -/
private theorem shift_entries_cons {c : MessageCache} {e : Cached} {es : List Cached}
    (h : c.entries = e :: es) (hlt : e.age + 1 < c.params.historyLength) :
    (MessageCache.shift c).entries
      = { e with age := e.age + 1 } :: es.filterMap (fun e =>
          if e.age + 1 < c.params.historyLength then some { e with age := e.age + 1 } else none) := by
  simp only [MessageCache.shift]
  rw [h]
  exact List.filterMap_cons_some (f := fun e => if e.age + 1 < c.params.historyLength
      then some { e with age := e.age + 1 } else none) (a := e) (l := es)
    (b := { e with age := e.age + 1 }) (by simp [hlt])

/-- A `put` entry stays at the head of the cache for `k` shifts, as long
as `k` is below `historyLength`. -/
private theorem shiftN_put_cons (c : MessageCache) (id : MessageId) (m : Message)
    (k : Nat) (hk : k < c.params.historyLength) :
    ∃ es, (MessageCache.shiftN (MessageCache.put c id m) k).entries
      = { id := id, topic := m.topic, message := m, age := k } :: es := by
  induction k with
  | zero => exact ⟨c.entries, rfl⟩
  | succ k ih =>
    have hk' : k < c.params.historyLength := by omega
    obtain ⟨es, hes⟩ := ih hk'
    have hparams : (MessageCache.shiftN (MessageCache.put c id m) k).params
        = c.params := by
      rw [shiftN_params]
      rfl
    have hlt : (⟨id, m.topic, m, k⟩ : Cached).age + 1
        < (MessageCache.shiftN (MessageCache.put c id m) k).params.historyLength := by
      rw [hparams]
      simpa using hk
    refine ⟨es.filterMap (fun e =>
      if e.age + 1 < (MessageCache.shiftN (MessageCache.put c id m) k).params.historyLength
      then some { e with age := e.age + 1 } else none), ?_⟩
    rw [shiftN_succ]
    exact shift_entries_cons hes hlt

/-- After `historyLength` shifts any cache is empty. Entries that start old
enough leave on the first shift, and the rest reach the bound by the last
one. -/
private theorem shiftN_entries_empty (c : MessageCache) :
    (MessageCache.shiftN c c.params.historyLength).entries = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  have hpos : 0 < c.params.historyLength := historyLength_pos c.params
  have hL : c.params.historyLength = (c.params.historyLength - 1) + 1 := by omega
  have hge : c.params.historyLength ≤ e.age := by
    have := shiftN_age_ge c c.params.historyLength e he
    omega
  have he' : e ∈ (MessageCache.shift (MessageCache.shiftN c (c.params.historyLength - 1))).entries := by
    rw [← shiftN_succ, ← hL]
    exact he
  have hlt := shift_age_lt he'
  rw [shiftN_params] at hlt
  omega

/-- A `put` entry is still found after any number of shifts below
`historyLength`. -/
theorem put_get_below_length_shifts (c : MessageCache) (id : MessageId) (m : Message)
    {k : Nat} (hk : k < c.params.historyLength) :
    MessageCache.get (MessageCache.shiftN (MessageCache.put c id m) k) id = some m := by
  obtain ⟨es, hes⟩ := shiftN_put_cons c id m k hk
  simp [MessageCache.get, hes]

/-- A `put` entry is gone after `historyLength` shifts. -/
theorem put_gone_after_length_shifts (c : MessageCache) (id : MessageId) (m : Message) :
    MessageCache.get (MessageCache.shiftN (MessageCache.put c id m) c.params.historyLength) id
      = none := by
  have h : (MessageCache.shiftN (MessageCache.put c id m) c.params.historyLength).entries = [] := by
    have hp := shiftN_entries_empty (MessageCache.put c id m)
    rwa [show (MessageCache.put c id m).params = c.params from rfl] at hp
  simp [MessageCache.get, h]

/-- Every id that gossip lists is an id that `get` finds. -/
theorem gossipIds_get_finds (c : MessageCache) (topic : TopicId) :
    ∀ id, id ∈ MessageCache.gossipIds c topic → ∃ m, MessageCache.get c id = some m := by
  intro id hid
  simp only [MessageCache.gossipIds, List.mem_map] at hid
  obtain ⟨e, he, rfl⟩ := hid
  rw [List.mem_filter] at he
  have hsome : (MessageCache.get c e.id).isSome := by
    simp only [MessageCache.get, Option.isSome_map, List.find?_isSome]
    exact ⟨e, he.1, by simp⟩
  exact Option.isSome_iff_exists.mp hsome

/-- A `put` keeps every entry inside the window bound. -/
theorem put_preserves_windowInvariant (c : MessageCache) (id : MessageId) (m : Message) :
    MessageCache.windowInvariant c → MessageCache.windowInvariant (MessageCache.put c id m) := by
  intro h e he
  rw [MessageCache.windowInvariant] at h
  simp only [MessageCache.put, List.mem_cons] at he
  rcases he with rfl | he
  · exact historyLength_pos c.params
  · exact h e he

/-- A `shift` keeps every entry inside the window bound. The input
invariant is not needed, because `shift` drops the entries that would
leave the window; the theorem keeps the hypothesis of the stated target. -/
theorem shift_preserves_windowInvariant (c : MessageCache) :
    MessageCache.windowInvariant c → MessageCache.windowInvariant (MessageCache.shift c) := by
  intro _ e he
  exact shift_age_lt (c := c) he

/-! ## The message index: the production message cache

`MessageCache` is the model, with the theorems above. Its `get` walks
every cached message, and the router calls it once per id of every
IHAVE and IWANT. `MessageIndex` is the structure the router runs: a
`HashMap` from id to the newest message and the heartbeat it was put
in, and one list of `(id, topic)` per history window, newest window
first. `shift` drops the oldest window, and erases an id of it only
when no later `put` renewed it.

The two agree on `get` and `gossipIds` after every sequence of `put`
and `shift`. The property test in `Tests/Gossipsub/Cache.lean` pins it
(CLAUDE.md, "Proofs and tests", rule 2). -/

/-- The production message cache. -/
structure MessageIndex where
  /-- The window counts, shared with the model. -/
  params : WindowParams
  /-- Each cached id: its newest message and the heartbeat of that put. -/
  byId : Std.HashMap MessageId (Message × Nat) := {}
  /-- One list of `(id, topic)` per window, newest window first, each
  newest first. At most `historyLength` windows. -/
  windows : List (List (MessageId × TopicId)) := [[]]
  /-- The heartbeats so far. -/
  tick : Nat := 0

namespace MessageIndex

/-- An empty index. -/
def empty (p : WindowParams) : MessageIndex := { params := p }

/-- Add a message to the current window: `MessageCache.put`. -/
def put (c : MessageIndex) (id : MessageId) (m : Message) : MessageIndex :=
  { c with byId := c.byId.insert id (m, c.tick)
           windows := match c.windows with
             | w :: ws => ((id, m.topic) :: w) :: ws
             | [] => [[(id, m.topic)]] }

/-- The newest message of the id: `MessageCache.get`. -/
def get (c : MessageIndex) (id : MessageId) : Option Message :=
  (c.byId.get? id).map (·.1)

/-- Shift one heartbeat: `MessageCache.shift`. The window that reaches
`historyLength` leaves, with each of its ids whose newest put was in
it. -/
def shift (c : MessageIndex) : MessageIndex :=
  let tick := c.tick + 1
  let windows := [] :: c.windows
  let kept := windows.take c.params.historyLength
  let gone := (windows.drop c.params.historyLength).flatten
  -- A put at heartbeat `t` has age `tick - t`. It leaves at age
  -- `historyLength`.
  let byId := gone.foldl (fun m (id, _) =>
    match m.get? id with
    | some (_, t) => if c.params.historyLength ≤ tick - t then m.erase id else m
    | none => m) c.byId
  { c with tick, windows := kept, byId }

/-- The ids gossip lists for a topic: `MessageCache.gossipIds`. -/
def gossipIds (c : MessageIndex) (topic : TopicId) : List MessageId :=
  ((c.windows.take c.params.historyGossip).flatten.filter (·.2 == topic)).map (·.1)

end MessageIndex

/-! ## Seen cache

The seen cache holds the message ids observed recently. An id is seen
while `at + ttl > now`, the spec `seen_ttl` of two minutes by default.
The cache is bounded: an add at capacity drops the oldest entry. A
re-add refreshes the entry to the newest position, the "timed least
recently used" rule of the spec.
-/

/-- The parameters of the seen cache. `capacity` bounds the entry count.
`ttl` is the spec `seen_ttl`. `valid` carries both positivity facts: a
zero `ttl` would make `add` write an entry that is never seen, and a zero
`capacity` would make the trim drop the entry just added. -/
structure SeenParams where
  /-- The largest number of entries the cache holds. -/
  capacity : Nat
  /-- The time an id counts as seen. -/
  ttl : Millis
  /-- The bound `0 < capacity` and `0 < ttl`. -/
  valid : 0 < capacity ∧ 0 < ttl
  deriving Repr

/-- One seen id and its insertion time. -/
structure SeenEntry where
  /-- The message id. -/
  id : MessageId
  /-- The time of the `add`. -/
  «at» : Millis
  deriving DecidableEq, Repr

/-- The seen cache: the parameters and the entries, newest first. -/
structure SeenCache where
  /-- The bounds. -/
  params : SeenParams
  /-- The seen ids, newest first. -/
  entries : List SeenEntry
  deriving Repr

/-- An empty cache with the given parameters. -/
def SeenCache.empty (p : SeenParams) : SeenCache :=
  { params := p, entries := [] }

/-- Whether the cache holds the id as seen at `now`. The check reads the
current time, so an entry expires between prunes. -/
def SeenCache.contains (c : SeenCache) (id : MessageId) (now : Millis) : Bool :=
  c.entries.any (fun e => decide (e.id = id ∧ e.at + c.params.ttl > now))

/-- Record the id as seen at `now`. The add removes the old entry of the
id, so a re-add moves the id to the newest position, and it trims the
list to `capacity`. The new entry is the head, so the trim drops the
oldest entries and never the new one. -/
def SeenCache.add (c : SeenCache) (id : MessageId) (now : Millis) : SeenCache :=
  { c with
    entries :=
      { id := id, «at» := now } ::
        (c.entries.filter (fun e => decide (e.id ≠ id))).take (c.params.capacity - 1) }

/-- Drop the entries whose `at + ttl` has passed. -/
def SeenCache.prune (c : SeenCache) (now : Millis) : SeenCache :=
  { c with entries := c.entries.filter (fun e => decide (e.at + c.params.ttl > now)) }

/-- The tail of an `add` never holds the added id, so `contains` reads the
new head alone. -/
private theorem contains_add_self (c : SeenCache) (id : MessageId) (t now : Millis) :
    SeenCache.contains (SeenCache.add c id t) id now = decide (t + c.params.ttl > now) := by
  have htail : ((c.entries.filter (fun e => decide (e.id ≠ id))).take
      (c.params.capacity - 1)).any
      (fun e => decide (e.id = id ∧ e.at + c.params.ttl > now)) = false := by
    rw [List.any_eq_false]
    intro e he
    have hsub : e ∈ c.entries.filter (fun e => decide (e.id ≠ id)) :=
      List.mem_of_mem_take he
    have hne : e.id ≠ id := of_decide_eq_true (List.mem_filter.mp hsub).2
    simp [hne]
  simp only [SeenCache.contains]
  rw [show (SeenCache.add c id t).params = c.params from rfl]
  simp only [SeenCache.add]
  rw [List.any_cons, htail, Bool.or_false]
  simp

/-- An add is seen at its own time. -/
theorem add_contains (c : SeenCache) (id : MessageId) (now : Millis) :
    SeenCache.contains (SeenCache.add c id now) id now = true := by
  rw [contains_add_self]
  have h : now < now + c.params.ttl := Nat.lt_add_of_pos_right c.params.valid.2
  simp [h]

/-- An id added at `t` is seen at every time below `t + ttl`. -/
theorem add_seen_below_ttl (c : SeenCache) (id : MessageId) (t t' : Millis)
    (_hle : t ≤ t') (hlt : t' < t + c.params.ttl) :
    SeenCache.contains (SeenCache.add c id t) id t' = true := by
  rw [contains_add_self]
  have h : t + c.params.ttl > t' := hlt
  simp [h]

/-- An id added at `t` is not seen at exactly `t + ttl`. -/
theorem add_unseen_at_ttl (c : SeenCache) (id : MessageId) (t : Millis) :
    SeenCache.contains (SeenCache.add c id t) id (t + c.params.ttl) = false := by
  rw [contains_add_self]
  simp

/-- An add never leaves more than `capacity` entries. -/
theorem add_bounded (c : SeenCache) (id : MessageId) (now : Millis) :
    (SeenCache.add c id now).entries.length ≤ c.params.capacity := by
  have hlen : (SeenCache.add c id now).entries.length
      = min (c.params.capacity - 1)
          (c.entries.filter (fun e => decide (e.id ≠ id))).length + 1 := by
    simp [SeenCache.add, List.length_take]
  rw [hlen]
  have hmin : min (c.params.capacity - 1)
      (c.entries.filter (fun e => decide (e.id ≠ id))).length ≤ c.params.capacity - 1 :=
    Nat.min_le_left _ _
  have hcap : 0 < c.params.capacity := c.params.valid.1
  omega

/-- A prune leaves only entries that are still live at `now`. -/
theorem prune_removes_expired (c : SeenCache) (now : Millis) :
    ∀ e ∈ (SeenCache.prune c now).entries, e.at + c.params.ttl > now := by
  intro e he
  simp only [SeenCache.prune, List.mem_filter] at he
  exact of_decide_eq_true he.2

/-! ## The seen index: the production seen cache

`SeenCache` is the model: a list, and the theorems above. Each of its
operations walks the whole list. At the default capacity of 65536 ids,
`contains` plus `add` costs about 50 ms a message
(etheorem/leanp2p#110, item 7). `SeenIndex` is the structure the router
runs: a `HashMap` from id to its add time, and a queue of `(id, number)`
in add order. A re-add leaves its old queue entry behind. An entry whose
number no longer matches the map is stale, and the front of the queue
skips it (lazy deletion).

The two agree on `contains` for every sequence of `add` and `prune`
whose times never go back, which is how the router calls them. The
property test in `Tests/Gossipsub/Cache.lean` pins it (CLAUDE.md,
"Proofs and tests", rule 2). With times that go back, a model `prune`
can drop an entry from the middle, and the index keeps it until it
reaches the front.

The index keys each id by its `IdKey`. A `MessageId` is a `List Nat`,
one heap cell per byte. A full index of 262144 ids of 20 bytes, the
consensus capacity, took about 166 MiB with list keys, 650 bytes an id,
and takes about 23 MiB with `IdKey`, 90 bytes an id. Both figures are
the peak resident memory above an empty index, in one run each. -/

/-- A message id as a map key. An id whose every value is a byte keeps
its bytes in a `ByteArray`. The model allows any `Nat` in an id, so an
id with a larger value keeps its list, and two different ids never share
a key. -/
inductive IdKey where
  | bytes (b : ByteArray)
  | wide (l : List Nat)
  deriving BEq, Hashable

/-- The key of an id. -/
def IdKey.of (id : MessageId) : IdKey :=
  if id.bytes.all (· < 256) then .bytes ⟨(id.bytes.map (·.toUInt8)).toArray⟩
  else .wide id.bytes

/-- The production seen cache. -/
structure SeenIndex where
  /-- The bounds, shared with the model. -/
  params : SeenParams
  /-- Each live id, by its key: its add time, and the number of its queue
  entry. -/
  index : Std.HashMap IdKey (Millis × Nat) := {}
  /-- `(id, number)` in add order, oldest first, stale entries included.
  The number tells a stale entry: a re-add in the same millisecond
  leaves two entries with one id and one time. The queue is two lists:
  `front` oldest first, and `back` newest first. A peek that finds
  `front` empty moves `back` over once and keeps the result, so each
  entry is reversed at most once. -/
  front : List (IdKey × Nat) := []
  /-- The newer half of the queue, newest first. -/
  back : List (IdKey × Nat) := []
  /-- The queue's length, stale entries included: the fuel of a walk. -/
  len : Nat := 0
  /-- The next entry number. -/
  next : Nat := 0

namespace SeenIndex

/-- An empty index. -/
def empty (p : SeenParams) : SeenIndex := { params := p }

/-- Whether the id is seen at `now`: `SeenCache.contains`. -/
def contains (c : SeenIndex) (id : MessageId) (now : Millis) : Bool :=
  match c.index.get? (IdKey.of id) with
  | some (t, _) => decide (t + c.params.ttl > now)
  | none => false

/-- Drop queue entries from the front while `drop` holds for the live
ones, at their add time, and erase each live one from the map. A stale
entry always goes. `fuel` bounds the walk by the queue's length. -/
def popWhile (fuel : Nat) (drop : SeenIndex → Millis → Bool) (c : SeenIndex) : SeenIndex :=
  match fuel with
  | 0 => c
  | fuel + 1 =>
    -- Move `back` over once when `front` runs out, and keep the move.
    let c := if c.front.isEmpty then { c with front := c.back.reverse, back := [] } else c
    match c.front with
    | [] => c
    | (id, n) :: rest =>
      match c.index.get? id with
      | some (t, n') =>
        if n' != n then popWhile fuel drop { c with front := rest, len := c.len - 1 }
        else if drop c t then
          popWhile fuel drop { c with index := c.index.erase id, front := rest, len := c.len - 1 }
        else c
      | none => popWhile fuel drop { c with front := rest, len := c.len - 1 }

/-- Record the id at `now`: `SeenCache.add`. Past the capacity, the
oldest live ids go. -/
def add (c : SeenIndex) (id : MessageId) (now : Millis) : SeenIndex :=
  let key := IdKey.of id
  let c := { c with index := c.index.insert key (now, c.next), back := (key, c.next) :: c.back,
                    len := c.len + 1, next := c.next + 1 }
  if c.index.size ≤ c.params.capacity then c
  else popWhile c.len (fun c _ => c.params.capacity < c.index.size) c

/-- Drop the expired ids: `SeenCache.prune`, for times that never go
back. -/
def prune (c : SeenIndex) (now : Millis) : SeenIndex :=
  popWhile c.len (fun c t => !(decide (t + c.params.ttl > now))) c

end SeenIndex

/-! ## Backoff table

The backoff table holds the period after a prune during which the router
does not regraft a peer for a topic. The spec extends the period when a
`GRAFT` arrives inside it, and this table's `add` is the write that both
sets and extends the period.
-/

/-- One backoff period: the pair and the time it ends. -/
structure BackoffEntry where
  /-- The peer. -/
  peer : Peer
  /-- The topic. -/
  topic : TopicId
  /-- The time the period ends. -/
  «until» : Millis
  deriving DecidableEq, Repr

/-- The backoff table: one entry per pair, newest first. -/
abbrev BackoffTable := List BackoffEntry

/-- An empty table. -/
def Backoff.empty : BackoffTable := []

/-- Set the backoff of the pair to end at `now + d`, and replace an older
period for the same pair. A prune, and a `GRAFT` inside the period, both
call this. -/
def Backoff.add (b : BackoffTable) (peer : Peer) (topic : TopicId)
    (d now : Millis) : BackoffTable :=
  { peer := peer, topic := topic, «until» := now + d } ::
    b.filter (fun e => decide (e.peer ≠ peer ∨ e.topic ≠ topic))

/-- Whether the pair is in backoff at `now`. The newest entry of the pair
decides, because `add` removes older entries of the same pair. -/
def Backoff.active (b : BackoffTable) (peer : Peer) (topic : TopicId)
    (now : Millis) : Bool :=
  match b.find? (fun e => decide (e.peer = peer ∧ e.topic = topic)) with
  | some e => decide (now < e.until)
  | none => false

/-- Drop the entries whose period has ended. -/
def Backoff.clear (b : BackoffTable) (now : Millis) : BackoffTable :=
  b.filter (fun e => decide (now < e.until))

/-- A pair added at `t` for `d` is active at every time below `t + d`. -/
theorem add_active_below (b : BackoffTable) (peer : Peer) (topic : TopicId)
    (d t now : Millis) (_hle : t ≤ now) (hlt : now < t + d) :
    Backoff.active (Backoff.add b peer topic d t) peer topic now = true := by
  simp [Backoff.active, Backoff.add, hlt]

/-- A pair added at `t` for `d` is not active at `t + d`. -/
theorem add_inactive_at_expiry (b : BackoffTable) (peer : Peer) (topic : TopicId)
    (d t : Millis) :
    Backoff.active (Backoff.add b peer topic d t) peer topic (t + d) = false := by
  simp [Backoff.active, Backoff.add]

/-- A second add for the same pair replaces the first period. -/
theorem add_overwrites (b : BackoffTable) (peer : Peer) (topic : TopicId)
    (d t d' t' now : Millis) (_hle : t' ≤ now) (hlt : now < t' + d') :
    Backoff.active (Backoff.add (Backoff.add b peer topic d t) peer topic d' t') peer topic now
      = true := by
  simp [Backoff.active, Backoff.add, hlt]

/-- If a `find?` finds an entry, and that entry satisfies `q`, then the
search for `q` together with the original predicate finds the same entry. -/
private theorem find?_and_of_find? {α : Type} (l : List α) (p q : α → Bool) {e : α}
    (h : l.find? p = some e) (hq : q e = true) :
    l.find? (fun x => decide (q x = true ∧ p x = true)) = some e := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    by_cases hpa : p a = true
    · rw [List.find?_cons_of_pos hpa] at h
      have hae : a = e := by injection h
      have hqa : q a = true := by rw [hae]; exact hq
      rw [List.find?_cons_of_pos (by simp [hpa, hqa]), hae]
    · rw [List.find?_cons_of_neg hpa] at h
      rw [List.find?_cons_of_neg (by simp [hpa])]
      exact ih h

/-- Clearing the expired entries keeps the active ones. -/
theorem clear_keeps_active (b : BackoffTable) (peer : Peer) (topic : TopicId)
    (now : Millis) (h : Backoff.active b peer topic now = true) :
    Backoff.active (Backoff.clear b now) peer topic now = true := by
  simp only [Backoff.active] at h
  split at h
  · rename_i e hfind
    have hlive : decide (now < e.until) = true := h
    have hand := find?_and_of_find? b (fun e => decide (e.peer = peer ∧ e.topic = topic))
      (fun e => decide (now < e.until)) hfind hlive
    have hfilter : (b.filter (fun e => decide (now < e.until))).find?
        (fun e => decide (e.peer = peer ∧ e.topic = topic)) = some e := by
      rw [List.find?_filter]
      exact hand
    simp only [Backoff.clear, Backoff.active, hfilter, hlive]
  · simp at h

/-- A clear leaves only entries whose period has not ended. -/
theorem clear_removes_expired (b : BackoffTable) (now : Millis) :
    ∀ e ∈ Backoff.clear b now, now < e.until := by
  intro e he
  simp only [Backoff.clear, List.mem_filter] at he
  exact of_decide_eq_true he.2

/-! ## IWANT promises

The router promises to answer an `IWANT` within a deadline. A delivery
of the id removes every promise for it. A promise whose deadline passed
without a delivery counts against the advertising peer, the input of the
`P₇` behavior penalty of the score part.
-/

/-- One in-flight promise: the peer that asked, the id it asked for, and
the time the answer is due. -/
structure IwantPromise where
  /-- The peer that asked. -/
  peer : Peer
  /-- The message id it asked for. -/
  id : MessageId
  /-- The time the answer is due. -/
  deadline : Millis
  deriving DecidableEq, Repr

/-- The promise table: one entry per pair, newest first. -/
abbrev PromiseTable := List IwantPromise

/-- Record a promise to `peer` for `id`, due at `deadline`. A second
promise for the same pair replaces the first, so the table holds one
deadline per pair. -/
def PromiseTable.promise (ps : PromiseTable) (peer : Peer) (id : MessageId)
    (deadline : Millis) : PromiseTable :=
  { peer := peer, id := id, deadline := deadline } ::
    ps.filter (fun e => decide (e.peer ≠ peer ∨ e.id ≠ id))

/-- The id arrived, so every promise for it is kept. -/
def PromiseTable.deliver (ps : PromiseTable) (id : MessageId) : PromiseTable :=
  ps.filter (fun e => decide (e.id ≠ id))

/-- The number of promises of one peer whose deadline is at or before
`now`. -/
private def countFor (ps : PromiseTable) (peer : Peer) (now : Millis) : Nat :=
  (ps.filter (fun e => decide (e.peer = peer ∧ e.deadline ≤ now))).length

/-- The peers of the promises whose deadline is at or before `now`, in
table order, with duplicates. -/
private def expiredPeers (ps : PromiseTable) (now : Millis) : List Peer :=
  (ps.filter (fun e => decide (e.deadline ≤ now))).map (fun e => e.peer)

/-- Boolean membership on a peer list, decided by `DecidableEq`. Core
`List` has no decidable membership instance, so the deduplication below
carries its own. -/
private def memPeer (p : Peer) (l : List Peer) : Bool :=
  l.any (fun q => decide (q = p))

private theorem memPeer_eq_true {p : Peer} {l : List Peer} :
    memPeer p l = true ↔ p ∈ l := by
  rw [memPeer, List.any_eq_true]
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← of_decide_eq_true hqp]
    exact hq
  · intro hp
    exact ⟨p, hp, by simp⟩

/-- Deduplicate a peer list, keeping the first occurrence of each peer. -/
private def dedupGo (seen : List Peer) : List Peer → List Peer
  | [] => []
  | p :: ps => if memPeer p seen then dedupGo seen ps else p :: dedupGo (p :: seen) ps

/-- Deduplicate a peer list. -/
private def dedupPeers (ps : List Peer) : List Peer := dedupGo [] ps

private theorem mem_dedupGo {p : Peer} {seen ps : List Peer} :
    p ∈ dedupGo seen ps ↔ p ∈ ps ∧ p ∉ seen := by
  induction ps generalizing seen with
  | nil => simp [dedupGo]
  | cons q qs ih =>
    simp only [dedupGo]
    split
    · rename_i hq
      have hqmem : q ∈ seen := memPeer_eq_true.mp hq
      rw [ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; exact absurd hqmem h2
        · exact ⟨h1, h2⟩
    · rename_i hq
      have hqmem : q ∉ seen := fun hc => hq (memPeer_eq_true.mpr hc)
      rw [List.mem_cons, ih]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro (h | ⟨h1, hne, h2⟩)
        · exact ⟨Or.inl h, fun hs => hqmem (h ▸ hs)⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · by_cases hpq : p = q
          · exact Or.inl hpq
          · exact Or.inr ⟨h1, hpq, h2⟩

private theorem mem_dedupPeers {p : Peer} {ps : List Peer} :
    p ∈ dedupPeers ps ↔ p ∈ ps := by
  rw [dedupPeers, mem_dedupGo]
  simp

/-- The peers with an expired promise, one pair per peer, with the number
of that peer's expired promises. A peer appears only when it has at least
one expired promise, and it appears once. This is the input of the `P₇`
behavior penalty. -/
def PromiseTable.broken (ps : PromiseTable) (now : Millis) : List (Peer × Nat) :=
  (dedupPeers (expiredPeers ps now)).map (fun p => (p, countFor ps p now))

/-- A promise records its pair and its deadline. -/
theorem promise_mem (ps : PromiseTable) (peer : Peer) (id : MessageId) (d : Millis) :
    ∃ e ∈ PromiseTable.promise ps peer id d, e.peer = peer ∧ e.id = id ∧ e.deadline = d :=
  ⟨_, List.mem_cons_self, rfl, rfl, rfl⟩

/-- A delivery leaves no promise that names the delivered id. -/
theorem deliver_removes (ps : PromiseTable) (id : MessageId) :
    ∀ e ∈ PromiseTable.deliver ps id, e.id ≠ id := by
  intro e he
  simp only [PromiseTable.deliver, List.mem_filter] at he
  exact of_decide_eq_true he.2

/-- A delivery keeps every promise of another id. -/
theorem deliver_keeps_others (ps : PromiseTable) (id : MessageId) :
    ∀ e, e ∈ ps → e.id ≠ id → e ∈ PromiseTable.deliver ps id := by
  intro e he hne
  rw [PromiseTable.deliver, List.mem_filter]
  exact ⟨he, by simpa using hne⟩

/-- `broken` names exactly the peers with an expired promise, with the
exact count. -/
theorem broken_mem_iff (ps : PromiseTable) (now : Millis) (peer : Peer) (n : Nat) :
    (peer, n) ∈ PromiseTable.broken ps now ↔
      n = (ps.filter (fun e => decide (e.peer = peer ∧ e.deadline ≤ now))).length ∧ 0 < n := by
  constructor
  · intro h
    rw [PromiseTable.broken, List.mem_map] at h
    obtain ⟨p, hp, hpn⟩ := h
    rw [Prod.mk.injEq] at hpn
    obtain ⟨hpe, hcnt⟩ := hpn
    subst hpe
    refine ⟨hcnt.symm, ?_⟩
    have hexp : p ∈ expiredPeers ps now := mem_dedupPeers.mp hp
    rw [expiredPeers, List.mem_map] at hexp
    obtain ⟨e, he, hep⟩ := hexp
    rw [List.mem_filter] at he
    have hle : e.deadline ≤ now := of_decide_eq_true he.2
    have hemem : e ∈ ps.filter (fun e => decide (e.peer = p ∧ e.deadline ≤ now)) := by
      rw [List.mem_filter]
      exact ⟨he.1, by simp [hep, hle]⟩
    have hpos : 0 < (ps.filter (fun e => decide (e.peer = p ∧ e.deadline ≤ now))).length :=
      List.length_pos_of_mem hemem
    rw [← hcnt]
    simpa [countFor] using hpos
  · rintro ⟨hn, hpos⟩
    rw [PromiseTable.broken, List.mem_map]
    have hpos' : 0 < (ps.filter (fun e => decide (e.peer = peer ∧ e.deadline ≤ now))).length := by
      rw [← hn]
      exact hpos
    obtain ⟨e, hemem⟩ := List.exists_mem_of_length_pos hpos'
    rw [List.mem_filter] at hemem
    obtain ⟨he, hcond⟩ := hemem
    obtain ⟨hpe, hle⟩ := of_decide_eq_true hcond
    have hexp : peer ∈ expiredPeers ps now := by
      rw [expiredPeers, List.mem_map]
      exact ⟨e, by rw [List.mem_filter]; exact ⟨he, by simp [hle]⟩, hpe⟩
    refine ⟨peer, mem_dedupPeers.mpr hexp, ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨rfl, by simpa [countFor] using hn.symm⟩

/-- After a delivery every count that `broken` reports excludes the
delivered id: a peer's count is exactly its expired promises for other
ids. -/
theorem broken_after_deliver_ignores_id (ps : PromiseTable) (id : MessageId) (now : Millis) :
    ∀ (peer : Peer) (n : Nat),
      (peer, n) ∈ PromiseTable.broken (PromiseTable.deliver ps id) now →
        n = (ps.filter (fun e =>
          decide (e.peer = peer ∧ e.id ≠ id ∧ e.deadline ≤ now))).length := by
  intro peer n hn
  have h := (broken_mem_iff (PromiseTable.deliver ps id) now peer n).mp hn
  obtain ⟨hcount, _⟩ := h
  rw [hcount]
  simp only [PromiseTable.deliver, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro a _
  by_cases h1 : a.peer = peer <;> by_cases h2 : a.id = id <;> by_cases h3 : a.deadline ≤ now <;>
    simp [h1, h2, h3]

end Libp2p.Protocols.Gossipsub.Cache
