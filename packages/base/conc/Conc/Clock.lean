import Conc.Select
import Conc.OnceRef

/-!
# `Clock`: the time seam

Time is a seam (ARCHITECTURE §3.1): a structure value that the code
calls through. Production code takes `Clock.system`, which reads the
monotonic clock and runs real timers. A test takes a `TestClock` and
moves time forward with `advance`, so a deadline test runs at once and
gives the same answer on every run.

A timer counts from `after`, so a loop that keeps selecting on one timer
still fires at its time.

A timer of the test clock is a channel that nobody sends on. `advance`
closes the channels of the timers that become due, and the close
completes their parks. The test timer thus keeps rule 1: a close wakes
every park.
-/

set_option autoImplicit false

namespace Conc

/-- The time seam. -/
structure Clock where
  /-- The time now, in milliseconds from an origin that the clock
  fixes. -/
  nowMs : BaseIO Nat
  /-- A park that completes `ms` milliseconds after this call. -/
  after : Nat → BaseIO (Park Unit)

/-- The production clock: the monotonic system clock, and real timers
on the same clock. A deadline does not move when the wall clock steps
(NTP, a manual change). -/
def Clock.system : Clock where
  nowMs := IO.monoMsNow
  after ms := Park.sleep ms ()

/-- Split timers into those due at `now` and the rest. `τ` is the type
of the timer, so the rule holds for any payload. -/
def takeDue {τ : Type} (now : Nat) (timers : List (Nat × τ)) :
    List (Nat × τ) × List (Nat × τ) :=
  timers.partition (·.1 ≤ now)

/-- No timer fires early. -/
theorem takeDue_due {τ : Type} {now : Nat} {timers : List (Nat × τ)} {t : Nat × τ}
    (h : t ∈ (takeDue now timers).1) : t.1 ≤ now := by
  simp only [takeDue, List.partition_eq_filter_filter, List.mem_filter,
    decide_eq_true_eq] at h
  exact h.2

/-- Every due timer leaves the list. -/
theorem takeDue_kept {τ : Type} {now : Nat} {timers : List (Nat × τ)} {t : Nat × τ}
    (h : t ∈ (takeDue now timers).2) : now < t.1 := by
  simp only [takeDue, List.partition_eq_filter_filter, List.mem_filter,
    Function.comp, Bool.not_eq_true', decide_eq_false_iff_not] at h
  omega

/-- The split loses no timer and adds none. -/
theorem takeDue_mem {τ : Type} {now : Nat} {timers : List (Nat × τ)} {t : Nat × τ} :
    (t ∈ (takeDue now timers).1 ∨ t ∈ (takeDue now timers).2) ↔ t ∈ timers := by
  simp only [takeDue, List.partition_eq_filter_filter, List.mem_filter]
  by_cases h : t.1 ≤ now <;> simp [h]

/-- The state of a test clock. -/
private structure TestClock.State where
  /-- The time now. -/
  now : Nat
  /-- The timers not yet due, each with its due time. -/
  timers : List (Nat × Chan Unit)
  /-- The number of `after` calls so far. -/
  armed : Nat
  /-- The number of `after` calls that `nextTimer` has taken. -/
  seen : Nat
  /-- True after `close`. -/
  closed : Bool

/-- A clock that moves only when the test calls `advance`. -/
structure TestClock where
  private state : OnceRef TestClock.State
  /-- A one-slot signal that `after` sends on, so `nextTimer` wakes. -/
  private signal : Chan Unit

namespace TestClock

/-- A test clock at time 0, with no timers. -/
def new : BaseIO TestClock :=
  return ⟨← OnceRef.new { now := 0, timers := [], armed := 0, seen := 0, closed := false },
    ← Chan.new 1⟩

/-- Wait until the code under test arms a timer that no earlier
`nextTimer` has taken. A test calls it before `advance`, so the advance
cannot run before the code arms the timer. A timer armed after the
advance could wait forever. `false` when the clock closes first. -/
def nextTimer (tc : TestClock) : Async Bool := do
  repeat
    -- The ascription marks the action `BaseIO`, so the lift applies
    -- (see `TaskSet.joinAll`).
    let took ← (tc.state.updateGet fun s =>
      if s.seen < s.armed then (true, { s with seen := s.seen + 1 }) else (false, s) :
      BaseIO Bool)
    if took then return true
    -- Park: `after` sends on `signal` after it counts the timer, and
    -- `close` closes `signal`. A signal that arrives between the count
    -- check and this receive waits in the slot, so no wakeup is lost.
    if (← tc.signal.recv).isNone then return false
  return false

/-- Move the time forward by `ms`, and fire every timer that becomes due.
One atomic step moves the time and removes the due timers, so a timer
that a concurrent `after` adds is either due now or kept. -/
def advance (tc : TestClock) (ms : Nat) : BaseIO Unit := do
  let due ← tc.state.updateGet fun s =>
    let now := s.now + ms
    let (due, rest) := takeDue now s.timers
    (due, { s with now, timers := rest })
  for (_, c) in due do
    c.close

/-- Close the clock: fire every pending timer, and wake every
`nextTimer`. A timer armed after the close fires at once. The test that
owns the clock calls it at the end, so no park on the clock outlives the
test, and the timer list does not outlive it either. -/
def close (tc : TestClock) : BaseIO Unit := do
  let pending ← tc.state.updateGet fun s => (s.timers, { s with timers := [], closed := true })
  for (_, c) in pending do
    c.close
  tc.signal.close

/-- The `Clock` seam value of the test clock. -/
def clock (tc : TestClock) : Clock where
  nowMs := return (← tc.state.get).now
  after ms := do
    -- Nobody sends on the channel. The close is the only event that
    -- its park sees.
    let fired : Chan Unit ← Chan.new 1
    let dueNow ← tc.state.updateGet fun s =>
      let s := { s with armed := s.armed + 1 }
      if ms = 0 || s.closed then (true, s)
      else (false, { s with timers := (s.now + ms, fired) :: s.timers })
    if dueNow then fired.close
    -- One slot: a pending signal already wakes `nextTimer`, which then
    -- reads the count, so a refused send loses nothing.
    discard <| tc.signal.trySend ()
    return Park.recv fired fun _ => ()

end TestClock

end Conc
