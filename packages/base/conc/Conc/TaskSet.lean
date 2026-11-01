import Conc.Chan
import Conc.Constants
import Conc.OnceRef

/-!
# `TaskSet`: the owner of a group of tasks

Every task has an owner that joins it (ARCHITECTURE §4.1, rule 2). The
runtime waits for every task at exit, so a task with no owner can keep
the process alive with nobody to end it. A `TaskSet` is the owner: it
spawns the tasks, and `joinAll` waits for them and gives their errors
to the caller. A swallowed error would hide a failed subsystem from the
shutdown path (the package ARCHITECTURE, "the three things the spike
missed").

The tasks are `Async` computations on the shared pool. A task that
parks holds no thread, so parked tasks add no threads, however many
tasks the set owns (`Conc.Wrap`, "Parks hold no thread").

## The count

A set holds no tasks. It holds a `Tally`: the number of live tasks and
the errors of the ended ones. Each task reports its own end, so an ended
task costs nothing, and memory follows the live tasks and
`maxTaskErrors`. An owner with a long life can spawn without a bound and
join only on close (PRINCIPLES 3.2).

Every change to the `Tally` is one atomic step. `spawn` counts the task
before the task exists, so `joinAll` can never read 0 while a task runs.
A task that spawns a child counts the child before the task ends, so the
count does not reach 0 between them.
-/

set_option autoImplicit false

namespace Conc

/-- The state of a set. `ε` is the type of a task error. -/
structure TaskSet.Tally (ε : Type) where
  /-- The tasks that started and have not ended. -/
  live : Nat
  /-- The first `maxTaskErrors` errors, in the order the tasks ended. -/
  errors : Array ε
  /-- The number of failed tasks, kept or not. -/
  failed : Nat

namespace TaskSet.Tally

variable {ε : Type}

/-- A task starts. -/
def start (s : Tally ε) : Tally ε :=
  { s with live := s.live + 1 }

/-- A task ends with the answer `r`. -/
def finish (r : Except ε Unit) (s : Tally ε) : Tally ε :=
  let s := { s with live := s.live - 1 }
  match r with
  | .ok () => s
  | .error e =>
    { s with
      failed := s.failed + 1
      errors := if s.errors.size < maxTaskErrors then s.errors.push e else s.errors }

/-- The report of `joinAll`: the errors and the failure count, once no
task is live. The report empties the tally. `none` while a task is
live, and the tally does not change. -/
def take (s : Tally ε) : Option (Array ε × Nat) × Tally ε :=
  if s.live = 0 then
    (some (s.errors, s.failed), { s with errors := #[], failed := 0 })
  else
    (none, s)

/-- A task that starts and ends leaves the live count as it was. -/
theorem finish_start_live (r : Except ε Unit) (s : Tally ε) :
    (finish r (start s)).live = s.live := by
  cases r <;> simp [finish, start]

/-- The end of a task lowers the live count by one. -/
theorem finish_live (r : Except ε Unit) (s : Tally ε) :
    (finish r s).live = s.live - 1 := by
  cases r <;> rfl

/-- A failed task always counts, kept or not. -/
theorem finish_failed (e : ε) (s : Tally ε) :
    (finish (.error e) s).failed = s.failed + 1 := rfl

/-- A task that succeeds changes no error count. -/
theorem finish_ok_failed (s : Tally ε) :
    (finish (.ok ()) s).failed = s.failed := rfl

/-- The kept errors never pass the bound. -/
theorem finish_errors_le (r : Except ε Unit) (s : Tally ε)
    (h : s.errors.size ≤ maxTaskErrors) :
    (finish r s).errors.size ≤ maxTaskErrors := by
  cases r with
  | ok _ => exact h
  | error e =>
    simp only [finish]
    split
    · simp only [Array.size_push]
      omega
    · exact h

/-- A later failure never removes a kept error. -/
theorem finish_errors_prefix (r : Except ε Unit) (s : Tally ε) :
    s.errors.toList <+: (finish r s).errors.toList := by
  cases r with
  | ok _ => exact List.prefix_refl _
  | error e =>
    simp only [finish]
    split
    · simp
    · exact List.prefix_refl _

/-- While a task is live, `joinAll` gets no report, and nothing changes. -/
theorem take_live (s : Tally ε) (h : s.live ≠ 0) : take s = (none, s) := by
  simp [take, h]

/-- With no live task, `joinAll` gets every kept error and the count. -/
theorem take_idle (s : Tally ε) (h : s.live = 0) :
    (take s).1 = some (s.errors, s.failed) := by
  simp [take, h]

end TaskSet.Tally

/-- A group of owned tasks. -/
structure TaskSet where
  private tally : OnceRef (TaskSet.Tally IO.Error)
  /-- The signal that the live count reached 0. -/
  private idle : Chan Unit

namespace TaskSet

/-- An empty set. -/
def new : BaseIO TaskSet :=
  return ⟨← OnceRef.new { live := 0, errors := #[], failed := 0 }, ← Chan.new 1⟩

/-- Record the end of a task, and signal when it was the last one. The
call never parks. -/
private def finish (ts : TaskSet) (r : Except IO.Error Unit) : BaseIO Unit := do
  let last ← ts.tally.updateGet fun s =>
    let s := Tally.finish r s
    (s.live == 0, s)
  if last then discard <| ts.idle.trySend ()

/-- Start `act` as a task of the set, on the shared pool. The set
records the end of the task and keeps no reference to it (module doc,
"The count"). A task that cannot start ends at once with its error. -/
def spawn (ts : TaskSet) (act : Async Unit) : BaseIO Unit := do
  ts.tally.update Tally.start
  Wrap.onEnd (← Wrap.spawn act) ts.finish

/-- Throw the report of a join. One failed task: its error. Several: one
error with the count of all of them and the text of the kept ones. -/
private def raise (errors : Array IO.Error) (failed : Nat) : Async Unit :=
  match errors.toList, failed with
  | _, 0 => return ()
  | [e], 1 => throw e
  | es, n => throw <| IO.userError s!"{n} tasks failed: {es.map toString}"

/-- Wait for every task of the set, and the tasks that they spawn into
the set while the join runs. With one failed task, the call throws its
error. With several, the call throws one error that counts them and
names the first `maxTaskErrors` in the order they ended. A task spawned
from outside the set after the join ends waits for the next `joinAll`.
Of two concurrent joins, one receives the errors. -/
def joinAll (ts : TaskSet) : Async Unit := do
  repeat
    -- `Async` unfolds to a `BaseIO` type, so Lean would read this
    -- `BaseIO` action as an `Async` one and fail. The ascription marks
    -- it `BaseIO`, and the lift applies.
    let report ← (ts.tally.updateGet Tally.take : BaseIO (Option (Array IO.Error × Nat)))
    if let some (errors, failed) := report then
      -- The token goes to a second join that parks here.
      discard <| (ts.idle.trySend () : BaseIO Bool)
      return ← raise errors failed
    -- Park: the end of the last task sends on `idle`. A task ends by
    -- itself, or by a close of what it parks on (rule 1). A token sent
    -- before this receive waits in the slot, so no wakeup is lost.
    discard ts.idle.recv

end TaskSet

end Conc
