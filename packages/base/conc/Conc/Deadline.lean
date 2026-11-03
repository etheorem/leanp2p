import Conc.Clock
import Conc.TaskSet

/-!
# `withinDeadline`

A deadline bounds a phase that may wait forever on a silent peer
(ARCHITECTURE §5.4). `withinDeadline` is a `select` over the work and a
timer of the clock. When the timer wins, it runs `onExpiry`, which
closes what the work parks on. The close wakes the work, the work ends
by itself, and `withinDeadline` joins it. Nothing cancels a task
(rule 1), and the work task has an owner that joins it on every exit
(rule 2).

`onExpiry` has the type `BaseIO Unit`, so a throw cannot leave the work
parked with nothing to wake it. `onExpiry` must still reach the park of
the work, or the join waits forever. A cancel would only hide that bug.
-/

set_option autoImplicit false

namespace Conc

/-- The two ways the race ends. `ρ` is the type of the work's answer. -/
inductive Race (ρ : Type) where
  | finished (r : ρ)
  | expired
  deriving DecidableEq, Repr

/-- The rule of a tie. `select` picks at random among ready parks, so
the timer can win while the work has already answered. `ready` is the
answer that waits in the channel after the race, and it turns the expiry
into a finish. A work that ended keeps its value, and its resources stay
open. -/
def Race.settle {ρ : Type} (race : Race ρ) (ready : Option ρ) : Race ρ :=
  match race, ready with
  | .finished r, _ => .finished r
  | .expired, some r => .finished r
  | .expired, none => .expired

/-- A finished race stays finished. -/
theorem Race.settleFinished {ρ : Type} (r : ρ) (ready : Option ρ) :
    (Race.finished r).settle ready = .finished r := rfl

/-- The work wins a tie: an answer in the channel turns the expiry into
that answer. -/
theorem Race.settleTie {ρ : Type} (r : ρ) :
    (Race.expired).settle (some r) = .finished r := rfl

/-- The deadline expires only when the timer won and no answer waits. -/
theorem Race.settleEqExpired {ρ : Type} (race : Race ρ) (ready : Option ρ) :
    race.settle ready = .expired ↔ race = .expired ∧ ready = none := by
  cases race <;> cases ready <;> simp [Race.settle]

/-- The answer of a finished work: its value, or a throw of its fault. -/
private def finish {α : Type} (r : Except IO.Error α) : Async (Except Error α) :=
  match r with
  | .ok a => return .ok a
  | .error e => throw e

/-- Give `release` the value that the work sent after it lost the race.
The call runs after the join, so the work has sent all it will send. -/
private def releaseLate {α : Type} (done : Chan (Except IO.Error α))
    (release : α → BaseIO Unit) : BaseIO Unit := do
  if let some (.ok a) ← done.tryRecv then release a

/-- Run `work` against a deadline of `ms` milliseconds on `clock`.

* The work ends first: the answer is its value, or the call throws its
  fault. When the work and the timer are ready at once, the work wins,
  and `onExpiry` does not run.
* The timer wins: `onExpiry` runs, the call waits for the work to end,
  and the answer is `.error .deadlineExpired`. The work ends because
  `onExpiry` closed what it parks on. Its own answer follows from the
  close: the call drops a fault, and a value goes to `release`.
* The `select` throws: `onExpiry` wakes the work, the call joins it,
  a value of the work goes to `release`, and the call throws the error
  of the `select`.

`release` exists for a work whose value holds a resource, such as a
connection. The work can end with a value after the timer won and
before `onExpiry` ran. No caller sees that value, so `release` frees
it. The default drops it, which suits a value that holds nothing. -/
def withinDeadline {α : Type} (clock : Clock) (ms : Nat)
    (onExpiry : BaseIO Unit) (work : Async α)
    (release : α → BaseIO Unit := fun _ => pure ()) : Async (Except Error α) := do
  -- Capacity 1: the work sends its one result and ends, with no park.
  let done : Chan (Except IO.Error α) ← Chan.new 1
  let owner ← TaskSet.new
  owner.spawn do
    -- The fault of the work travels as data, so the race sees it.
    let r : Except IO.Error α ← try .ok <$> work catch e => pure (.error e)
    discard <| done.send r
  let timer ← clock.after ms
  let race : Race (Except IO.Error α) ← try
      -- Park: the send of the work wakes it, and so does the timer.
      -- Nobody closes `done`, so its `none` arm cannot occur. It maps to
      -- `expired` to keep the function total.
      select #[
        Park.recv done (fun | some r => .finished r | none => .expired),
        timer.map fun () => .expired]
    catch e =>
      onExpiry
      owner.joinAll
      releaseLate done release
      throw e
  -- A race that the work won has emptied `done`, so `settle` keeps it.
  match race.settle (← done.tryRecv) with
  | .finished r =>
    owner.joinAll
    finish r
  | .expired =>
    onExpiry
    -- The close of `onExpiry` wakes the work. The join waits for it.
    owner.joinAll
    -- The work has ended. An answer that it sent after the `tryRecv`
    -- above waits in `done`.
    releaseLate done release
    return .error .deadlineExpired

/-- A read with a bound. `c.close` is the close that reaches the park of
the work. The 30 s value is an example, and it belongs to the caller. -/
example (clock : Clock) (c : Chan Nat) : Async (Except Error (Option Nat)) :=
  withinDeadline clock 30000 c.close c.recv

end Conc
