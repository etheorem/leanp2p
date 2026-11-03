import Conc.OnceRef
import Conc.Wrap

/-!
# `Outcome`: how a session ended

A session of ARCHITECTURE §3.3 runs a loop and the tasks that serve it
over one connection. Its owner learns how it ended after the tasks have
ended. Two facts decide the answer (§3.5):

* The loop's answer: `.ok ()` for an orderly end, or the protocol error
  of its core.
* The first fault of the connection while the session ran: a failed
  read or write.

A fault under an orderly answer reaches the owner as the thrown
`IO.Error`. A fault after the end reports nothing new. The teardown and
the owner's close shut the connection, so the reads and writes after
them fail. `Outcome` holds both facts and that rule in one atomic cell.

## The owner's close

A shell whose `close` shuts the connection at once marks the outcome
first (`markClosing`). A write that the close interrupts then fails
after the end, and `answer` reports an orderly end. Without the mark,
the writer could record that failure before the loop's teardown set the
answer, and `answer` would report a fault the owner caused. A `close`
that lets the writer flush before it shuts the connection needs no
mark.
-/

set_option autoImplicit false

namespace Conc

/-- The facts of a session's end. `ε` is the protocol error of the
session, and `φ` is the type of a fault. -/
structure Outcome.State (ε φ : Type) where
  /-- The loop's answer, once the loop has ended. -/
  result : Option (Except ε Unit)
  /-- The first fault of the connection while the session ran. -/
  fault : Option φ
  /-- The first failed write while the session ran. A shell that reports
  a failed write in its own way records it here, apart from `fault`. -/
  writeFault : Option φ
  /-- The owner closed the session. -/
  closing : Bool

/-- A session's end, in one atomic cell, so the check of the end and the
record of a fault are one step. -/
structure Outcome (ε : Type) where
  private state : OnceRef (Outcome.State ε IO.Error)

namespace Outcome

variable {ε : Type}

/-- The rule of a fault cell: a session that has ended records nothing,
and the first fault stays. `φ` is the type of the fault. -/
def record {φ : Type} (ended : Bool) (cell : Option φ) (e : φ) : Option φ :=
  if ended then cell else cell <|> some e

/-- After the end, the cell does not change. -/
theorem recordEnded {φ : Type} (cell : Option φ) (e : φ) :
    record true cell e = cell := rfl

/-- A later fault never replaces the first one. -/
theorem recordKeeps {φ : Type} (a e : φ) (ended : Bool) :
    record ended (some a) e = some a := by
  cases ended <;> rfl

/-- The session has ended: the loop has answered, or the owner has
closed the session. -/
def State.ended {φ : Type} (s : State ε φ) : Bool :=
  s.result.isSome || s.closing

/-- Record a fault of the connection. -/
def State.recordFault {φ : Type} (e : φ) (s : State ε φ) : State ε φ :=
  { s with fault := record s.ended s.fault e }

/-- Record a failed write. -/
def State.recordWriteFault {φ : Type} (e : φ) (s : State ε φ) : State ε φ :=
  { s with writeFault := record s.ended s.writeFault e }

/-- After the end, a fault changes nothing. -/
theorem State.recordFaultEnded {φ : Type} (e : φ) (s : State ε φ) (h : s.ended = true) :
    s.recordFault e = s := by
  simp [recordFault, h, recordEnded]

/-- After the end, a failed write changes nothing. -/
theorem State.recordWriteFaultEnded {φ : Type} (e : φ) (s : State ε φ)
    (h : s.ended = true) : s.recordWriteFault e = s := by
  simp [recordWriteFault, h, recordEnded]

/-- While the session runs, a cell that holds a fault keeps it through
any list of later faults. -/
theorem foldlRecordSome {φ : Type} (a : φ) (es : List φ) :
    es.foldl (record false) (some a) = some a := by
  induction es with
  | nil => rfl
  | cons _ _ ih => simpa [recordKeeps] using ih

/-- While the session runs, the cell holds the first fault of the
list. -/
theorem foldlRecordNone {φ : Type} (es : List φ) :
    es.foldl (record false) none = es.head? := by
  cases es with
  | nil => rfl
  | cons e es => simpa [record] using foldlRecordSome e es

/-- The rule of the answer (§3.5): `.error` is the fault to throw, and
`.ok` is the answer to return. A session with no answer yet reads as
orderly. -/
def joinAnswer {φ : Type} (fault : Option φ) (result : Option (Except ε Unit)) :
    Except φ (Except ε Unit) :=
  match fault, result.getD (.ok ()) with
  | some e, .ok () => .error e
  | _, r => .ok r

/-- A fault under an orderly answer becomes the fault to throw. -/
theorem joinAnswerFault {φ : Type} (e : φ) :
    joinAnswer (ε := ε) (some e) (some (.ok ())) = .error e := rfl

/-- A protocol error stays the answer, with or without a fault. -/
theorem joinAnswerProtocol {φ : Type} (fault : Option φ) (p : ε) :
    joinAnswer fault (some (.error p)) = .ok (.error p) := by
  cases fault <;> rfl

/-- With no fault, the answer is the loop's answer. -/
theorem joinAnswerOrderly {φ : Type} (r : Except ε Unit) :
    joinAnswer (none : Option φ) (some r) = .ok r := rfl

/-- The outcome of a session that runs. -/
def new : BaseIO (Outcome ε) :=
  return ⟨← OnceRef.new
    { result := none, fault := none, writeFault := none, closing := false }⟩

/-- Record a fault of the connection, unless the session has ended. The
first fault stays. One atomic step checks the end and records the fault.
The teardown calls `finish`, and the owner's close calls `markClosing`,
before either one closes the connection. A read or a write that the
close breaks therefore fails after the end, and it records nothing. -/
def recordFault (o : Outcome ε) (e : IO.Error) : BaseIO Unit :=
  o.state.update (State.recordFault e)

/-- Record a failed write, by the rule of `recordFault`, in the slot
that `writeFault` reads. -/
def recordWriteFault (o : Outcome ε) (e : IO.Error) : BaseIO Unit :=
  o.state.update (State.recordWriteFault e)

/-- The first failed write. A shell reads it after the tasks have ended. -/
def writeFault (o : Outcome ε) : BaseIO (Option IO.Error) :=
  return (← o.state.get).writeFault

/-- Mark the owner's close (module doc, "The owner's close"). -/
def markClosing (o : Outcome ε) : BaseIO Unit :=
  o.state.update fun s => { s with closing := true }

/-- Set the loop's answer. The teardown calls it once. -/
def finish (o : Outcome ε) (r : Except ε Unit) : BaseIO Unit :=
  o.state.update fun s => { s with result := some r }

/-- The answer for the owner, after the tasks have ended: the loop's
answer, but a fault under an orderly answer throws (§3.5). -/
def answer (o : Outcome ε) : Async (Except ε Unit) := do
  -- The ascription marks the read `BaseIO`, so the lift into `Async`
  -- applies (see `Conc.TaskSet.joinAll`).
  let s ← (o.state.get : BaseIO (State ε IO.Error))
  match joinAnswer s.fault s.result with
  | .error e => throw e
  | .ok r => return r

end Outcome

end Conc
