import Conc.Chan
import Conc.Clock
import Conc.OnceRef
import Conc.Select

/-!
# `Alarm`: a wake at the due time a loop asked for last

A core never reads the clock (ARCHITECTURE §3.3): it asks for its next
tick with a due time, and a task of the shell sleeps until then and
posts the tick. Any loop with timers needs that task, so it has one
home here.

The loop calls `set` with each new due time, and `set` never parks. A
later `set` replaces the earlier due time. The task, `run`, sleeps on
the `Clock` until the due time or until the next `set`, whichever comes
first, so nothing polls. `close` ends the task: the close of the signal
wakes its park (PRINCIPLES 3.1).
-/

set_option autoImplicit false

namespace Conc

/-- The due time a loop asked for last, and the signal that it changed.
The signal has room for one token, so the signals of a burst of `set`s
join into one. -/
structure Alarm where
  /-- The time of the next wake, in the clock's milliseconds. -/
  private due : OnceRef (Option Nat)
  /-- The signal that `due` changed. `close` closes it. -/
  private signal : Chan Unit

namespace Alarm

/-- An alarm with no due time. -/
def new : BaseIO Alarm :=
  return { due := ← OnceRef.new none, signal := ← Chan.new 1 }

/-- Ask for a wake at `t`, in place of the earlier due time. -/
def set (a : Alarm) (t : Nat) : BaseIO Unit := do
  a.due.set (some t)
  discard <| a.signal.trySend ()

/-- End `run`: the close of the signal wakes it. -/
def close (a : Alarm) : BaseIO Unit :=
  a.signal.close

/-- What woke `run`. -/
private inductive Wake where
  /-- `set` asked for a new due time. -/
  | request
  /-- The due time came. -/
  | due
  /-- `close` closed the signal. -/
  | closed

/-- The due time after the wake for `fired`. A `set` that came meanwhile
with another time keeps that time. A `set` of the same time counts as
served. -/
def clearDue (fired current : Option Nat) : Option Nat :=
  if current == fired then none else current

/-- The wake clears the due time that it served. -/
theorem clearDueServed (fired : Option Nat) : clearDue fired fired = none := by
  simp [clearDue]

/-- A different due time from a later `set` survives the wake. -/
theorem clearDueLater {fired current : Option Nat} (h : current ≠ fired) :
    clearDue fired current = current := by
  simp [clearDue, h]

/-- The task of the alarm. It sleeps until the due time asked for last,
and then calls `fire` with the time on `clock`. It ends at `close`, or
when `fire` answers `.error`, since the loop then takes no more
events. -/
def run (a : Alarm) (clock : Clock) (fire : Nat → Async (Except Error Unit)) : Async Unit := do
  -- The timer and the due time it serves. A wake with the same due time
  -- keeps this timer, so each due time arms one timer.
  let mut armed : Option (Nat × Park Unit) := none
  repeat
    let due ← (a.due.get : BaseIO (Option Nat))
    if armed.map (·.1) != due then
      armed ← match due with
        | none => pure none
        | some t =>
          let left := t - (← (clock.nowMs : BaseIO Nat))
          pure (some (t, ← (clock.after left : BaseIO (Park Unit))))
    let onSignal := Park.recv a.signal fun
      | some _ => Wake.request
      | none => Wake.closed
    -- Park: the due time wakes it, so does a new request, and `close`
    -- closes the signal.
    let woke ← match armed with
      | none => select #[onSignal]
      | some (_, timer) => select #[onSignal, timer.map fun _ => Wake.due]
    match woke with
    | .closed => break
    | .request => pure ()
    | .due =>
      -- The loop asks again after the wake if it needs one. A request
      -- that came meanwhile stays.
      a.due.update (clearDue due)
      armed := none
      if let .error _ ← fire (← (clock.nowMs : BaseIO Nat)) then break

end Alarm

end Conc
