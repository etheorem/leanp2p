import Std.Data.HashMap
import Conc
import Streams.Error

/-!
# `Stream`: the application view over a muxer loop

A muxer session is a pure core and one loop task (ARCHITECTURE §3.3).
The application never touches the loop. It holds a `Stream`, a seam
(§3.1) whose fields talk to the loop through channels:

* `read` takes from the inbox of the stream, a `Chan` that the loop
  fills and the muxer bounds. Then it posts the count of the bytes that
  it took.
* `write`, `close`, and `reset` post events to the loop.

This module holds the parts that every muxer shares, so each fact has
one home (§3.8):

* `Stream`, the seam itself.
* `Completions`, the table that matches each answer to its request by
  tag.
* `LoopPort`, what a muxer shell gives one stream, and `Stream.ofPort`,
  which builds the stream from it.
* `Stream.prependBytes`, the hand-over of §4.7 at the stream level.

The muxer owns its `Event` and `Action` types. Its shell builds the
`LoopPort` closures that wrap its own events, so this module needs no
protocol knowledge.

## Tagged completions

A write returns only after the loop puts its bytes on the wire, so
the back-pressure stays exact (§5.1). The core cannot hold a promise
(§3.3), so the shell matches the answers by tag:

1. `Stream.write` takes a fresh tag and its answer slot from the
   `Completions` of the session.
2. It posts the write event with the tag, and parks on the slot.
3. The core answers the event with a done or a refused action for the
   tag. The shell performs the action with `Completions.resolve`.

An answer slot is a `Chan` of capacity 1 that takes one value and then
closes. A close wakes the parked writer (PRINCIPLES 3.1). When the loop
ends, its owner calls `Completions.closeAll`, and every writer that
still parks wakes with `.error .closed`.

## The tag table as a pure state

The table changes in three steps, `register`, `resolve`, and
`closeAll`. Each step is a pure function of `Completions.State`, and
the shell applies it in one `OnceRef.updateGet` (§4.1, rule 3). So the
rules are theorems:

* A tag is fresh when the table gives it.
* An answer retires its tag, and a second answer finds nothing.
* A closed table gives no tag.
-/

set_option autoImplicit false

namespace Streams

open Conc

/-- The application view of one muxed stream. -/
structure Stream where
  /-- The next chunk. `.ok none` at the end of the stream: the peer
  closed its write direction. `.error .reset` when the stream was reset.
  After an error the stream is dead, and the reads after it answer
  `.ok none`. -/
  read : Async (Except Error (Option ByteArray))
  /-- Write the bytes, and return when they are on the wire.
  `.error` when the loop refused them, or when the session ended. -/
  write : ByteArray → Async (Except Error Unit)
  /-- Close our write direction (half-close, §5.3). The read direction
  stays open until the peer closes it. -/
  close : Async Unit
  /-- Stop both directions. -/
  reset : Async Unit

/-! ## The tag table -/

/-- The state of a tag table. `σ` is the type of an answer slot, so the
steps below are pure, and a test or a theorem can use any type. -/
structure Completions.State (σ : Type) where
  /-- The next free tag. -/
  next : Nat
  /-- The answer slot of each request that waits. -/
  waiting : Std.HashMap Nat σ
  /-- True after `closeAll`. -/
  closed : Bool

namespace Completions.State

variable {σ : Type}

/-- An empty, open table. -/
def empty : State σ :=
  { next := 0, waiting := {}, closed := false }

/-- Give a fresh tag to a request with the answer slot `slot`. A closed
table gives no tag, and nothing changes. -/
def register (slot : σ) (s : State σ) : Option Nat × State σ :=
  if s.closed then (none, s)
  else (some s.next, { s with next := s.next + 1, waiting := s.waiting.insert s.next slot })

/-- Take the slot of `tag` out of the table. `none` when the tag waits
no more: it was answered already, or the table is closed. -/
def resolve (tag : Nat) (s : State σ) : Option σ × State σ :=
  (s.waiting.get? tag, { s with waiting := s.waiting.erase tag })

/-- Close the table: take every slot that waits, and give no tag from
now on. -/
def closeAll (s : State σ) : List (Nat × σ) × State σ :=
  (s.waiting.toList, { s with waiting := {}, closed := true })

/-- The freshness invariant: every waiting tag is below `next`. -/
def Fresh (s : State σ) : Prop :=
  ∀ k, k ∈ s.waiting → k < s.next

/-- The empty table is fresh. -/
theorem freshEmpty : (empty : State σ).Fresh := by
  intro k hk
  simp [empty] at hk

/-- A closed table gives no tag, and nothing changes. -/
theorem registerClosed (slot : σ) (s : State σ) (h : s.closed = true) :
    register slot s = (none, s) := by
  simp [register, h]

/-- An open table gives `next` as the tag. -/
theorem registerOpen (slot : σ) (s : State σ) (h : s.closed = false) :
    (register slot s).1 = some s.next := by
  simp [register, h]

/-- In a fresh table, the tag that `register` gives waits nowhere yet:
two requests never share a tag. -/
theorem nextNotMem (s : State σ) (h : s.Fresh) : s.next ∉ s.waiting := by
  intro hm
  have := h s.next hm
  omega

/-- `register` keeps the table fresh. -/
theorem freshRegister (slot : σ) (s : State σ) (h : s.Fresh) :
    (register slot s).2.Fresh := by
  unfold register
  split
  · exact h
  · intro k hk
    simp only [Std.HashMap.mem_insert, beq_iff_eq] at hk
    rcases hk with rfl | hk
    · simp
    · have := h k hk
      simp only
      omega

/-- After an answer, the tag waits no more. -/
theorem notMemResolve (tag : Nat) (s : State σ) : tag ∉ (resolve tag s).2.waiting := by
  simp [resolve]

/-- A second answer for one tag finds no slot, so a slot takes one
answer at most. -/
theorem resolveResolve (tag : Nat) (s : State σ) :
    (resolve tag (resolve tag s).2).1 = none := by
  simp [resolve]

/-- `resolve` keeps the table fresh. -/
theorem freshResolve (tag : Nat) (s : State σ) (h : s.Fresh) : (resolve tag s).2.Fresh := by
  intro k hk
  simp only [resolve, Std.HashMap.mem_erase] at hk
  exact h k hk.2

/-- `resolve` keeps the closed flag. -/
@[simp] theorem closedResolve (tag : Nat) (s : State σ) :
    (resolve tag s).2.closed = s.closed := rfl

/-- After `closeAll`, the table is closed, and no slot waits. -/
theorem closeAllClosed (s : State σ) :
    (closeAll s).2.closed = true ∧ ∀ k, k ∉ (closeAll s).2.waiting := by
  simp [closeAll]

/-- After `closeAll`, `register` gives no tag. -/
theorem registerCloseAll (slot : σ) (s : State σ) :
    (register slot (closeAll s).2).1 = none := by
  simp [register, closeAll]

/-- `closeAll` keeps the table fresh. -/
theorem freshCloseAll (s : State σ) : (closeAll s).2.Fresh := by
  intro k hk
  simp [closeAll] at hk

end Completions.State

/-- The tags of one kind of request in one session, with the answer slot
of each. The writes of every stream share one table, so a tag names one
write in the whole session. A muxer that answers another request by tag,
such as the open of a stream with the `Stream` itself, keeps a second
table with that answer type. -/
structure Completions (α : Type) where
  private state : OnceRef (Completions.State (Chan (Except Error α)))

namespace Completions

variable {α : Type}

/-- An empty table. -/
def new : BaseIO (Completions α) :=
  return ⟨← OnceRef.new .empty⟩

/-- A fresh tag, and the slot that its answer arrives on. `none` after
`closeAll`: the session ended, and no answer will come. -/
def register (c : Completions α) : BaseIO (Option (Nat × Chan (Except Error α))) := do
  -- A closed table needs no slot, so a writer that keeps writing after
  -- the end allocates nothing. `State.register` checks the flag again,
  -- since a `closeAll` can come between the two steps.
  if (← c.state.get).closed then return none
  let slot : Chan (Except Error α) ← Chan.new 1
  let tag ← c.state.updateGet (State.register slot)
  return tag.map (·, slot)

/-- Answer the request of `tag`, and retire the tag. An unknown tag does
nothing: the request was answered already, or the table is closed. -/
def resolve (c : Completions α) (tag : Nat) (answer : Except Error α) : BaseIO Unit := do
  if let some slot ← c.state.updateGet (State.resolve tag) then
    -- The slot has room for this one answer, so the send never parks.
    discard <| slot.trySend answer
    slot.close

/-- Close the table. Every request that waits wakes with
`.error .closed`, and `register` answers `none` from now on. The owner
of the loop calls it when the loop ends. A second call does nothing. -/
def closeAll (c : Completions α) : BaseIO Unit := do
  for (_, slot) in ← c.state.updateGet State.closeAll do
    slot.close

end Completions

/-! ## Building a stream -/

/-- What a muxer shell gives one stream: the inbox that the loop fills,
the tag table of the session, and the closures that post the events of
this stream to the loop. A post answers `.error .closed` after the loop
ends. -/
structure LoopPort where
  /-- The chunks that the loop delivers. The loop sends `.error .reset`
  on a reset, and closes the inbox at the end of the stream. -/
  inbox : Chan (Except Error ByteArray)
  /-- Why the stream ended, when a reset came after the inbox closed. A
  read that finds the inbox closed answers this reason in place of EOF.
  The default is no reason, so a closed inbox reads as EOF. A muxer
  whose spec makes every read after a reset an error sets it. -/
  endedBy : BaseIO (Option Error) := pure none
  /-- The write tags of the session. -/
  completions : Completions Unit
  /-- Post a write of the bytes under the tag. -/
  postWrite : Nat → ByteArray → Async (Except Conc.Error Unit)
  /-- Post that the application took `n` delivered bytes. A muxer with
  flow control returns the credit to the peer here. A muxer without
  flow control answers at once. The field has no default, so a muxer
  with flow control cannot leave it out. -/
  postConsumed : Nat → Async (Except Conc.Error Unit)
  /-- Post a half-close. -/
  postClose : Async (Except Conc.Error Unit)
  /-- Post a reset. -/
  postReset : Async (Except Conc.Error Unit)

namespace Stream

/-- The stream that a loop serves through `port`.

The stream keeps one flag of its own: it is dead after a read answers
an error. The reads after that answer `.ok none` at once, as
`Stream.read` promises, whether or not the loop closed the inbox. A
muxer that keeps the inbox open after a reset cannot break the
promise. -/
def ofPort (port : LoopPort) : BaseIO Stream := do
  let dead : OnceRef Bool ← OnceRef.new false
  return {
  read := do
    if ← (dead.get : BaseIO Bool) then return .ok none
    -- Park: a delivery of the loop wakes it, and so does the close of
    -- the inbox.
    match ← port.inbox.recv with
    | some (.ok chunk) =>
      -- The bytes left the inbox, so the muxer can return their credit.
      -- A loop that ended takes no post, and needs none.
      discard <| port.postConsumed chunk.size
      return .ok (some chunk)
    | some (.error e) =>
      dead.set true
      return .error e
    | none =>
      -- The inbox closed at the end of the stream. A reset after that
      -- close is in the port.
      match ← (port.endedBy : BaseIO (Option Error)) with
      | some e =>
        dead.set true
        return .error e
      | none => return .ok none
  write := fun bytes => do
    let some (tag, slot) ← port.completions.register | return .error .closed
    if let .error _ ← port.postWrite tag bytes then
      -- The loop ended and will never answer: retire the tag.
      port.completions.resolve tag (.error .closed)
      return .error .closed
    -- Park: `resolve` sends the answer and closes the slot, and
    -- `closeAll` closes it with no answer.
    match ← slot.recv with
    | some answer => return answer
    | none => return .error .closed
  close := discard port.postClose
  reset := discard port.postReset }

/-- The stream with `front` ahead of the bytes that it delivers. The
negotiation of a stream can read past its last message. Those bytes
belong to the application, and this function puts them in front of the
stream (§4.7). The first read answers `front` whole. -/
def prependBytes (s : Stream) (front : ByteArray) : BaseIO Stream := do
  if front.isEmpty then return s
  let pending : OnceRef ByteArray ← OnceRef.new front
  return { s with
    read := do
      -- One atomic step takes the bytes out, so two reads cannot both
      -- answer them. The ascription marks the step `BaseIO`, so the
      -- lift into `Async` applies (see `Conc.TaskSet.joinAll`).
      let taken ← (pending.updateGet fun b => (b, .empty) : BaseIO ByteArray)
      if taken.isEmpty then s.read else return .ok (some taken) }

end Stream

end Streams
