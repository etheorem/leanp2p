import Conc.Chan

/-!
# `select`: the first of several parks

`select` waits for the first of several parks to complete (ARCHITECTURE
§4.1). It replaces every hand-rolled first-of loop of the stack (§9,
delta 5). A `Park` is a receive on a channel or a timer. A close of the
channel completes its receive park, so every park that `select` waits on
has a close that reaches it (PRINCIPLES 3.1).
-/

set_option autoImplicit false

namespace Conc

/-- One event that `select` can wait for, with the map of its result. -/
structure Park (α : Type) where
  private raw : Wrap.RawPark α

namespace Park

variable {α β : Type}

/-- The park on the next receive of `c`. `k` maps the value, or `none`
when `c` is closed and empty. -/
def recv (c : Chan β) (k : Option β → α) : Park α :=
  ⟨c.recvPark k⟩

/-- The park on a timer of the monotonic clock. The timer is due `ms`
milliseconds after this call. This call fixes the due time, so a
`select` that loses does not restart the count. Production code takes
its timers from a `Clock`, so a test can drive time. -/
def sleep (ms : Nat) (k : α) : BaseIO (Park α) :=
  return ⟨Wrap.RawPark.sleepUntil ((← IO.monoMsNow) + ms) k⟩

/-- Map the result of a park. -/
def map (f : α → β) (p : Park α) : Park β :=
  ⟨p.raw.map f⟩

end Park

/-- Wait for the first park that completes, and return its result. When
several are ready, the choice is random, so no park starves the others.
`Std` throws on an empty array, so the call takes a proof that the array
is not empty. `simp` proves it for a literal array, so a call reads
`select #[a, b]`. -/
def select {α : Type} (parks : Array (Park α)) (_h : 0 < parks.size := by simp) :
    Async α :=
  Wrap.selectOne (parks.map (·.raw))

/-- The usual call: the default argument proves the literal array is not
empty. -/
example (c : Chan Nat) : Async (Option Nat) :=
  select #[Park.recv c id]

end Conc
