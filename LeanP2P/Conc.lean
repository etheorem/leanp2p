import Std.Sync.Channel
import Std.Sync.Mutex
/-!
# Concurrency core (VECTOR_TEST_PLAN.md, phase 4 step 22)

Replaces the spike's polling queues (`IO.Ref` + `IO.sleep` loops, racy
read-modify-write) with blocking primitives:

- `Chan` wraps `Std.CloseableChannel`: FIFO with EOF; `recv` parks the task
  on a promise instead of polling, `close` wakes every waiter (`none`).
- `TaskSet` is the single place that owns spawned tasks: every task has an
  owner, and the owner joins them on close (Lean's RTS waits for all tasks
  at exit, so nothing may be left parked).
- `OnceRef` is a mutex-guarded cell for the read-modify-write updates the
  old `IO.Ref` code did unsynchronized.

With this, the whole stack is correct under `+RTS -N1` (no starvation:
nothing spins) and under contention (no lost updates).
-/

namespace LeanP2P

/-! ## Chan: FIFO with EOF -/

/-- A closeable FIFO channel. `send` is non-blocking (unbounded buffer,
`false` once closed); `recv` blocks until a value or close. -/
structure Chan (α : Type) where
  ch : Std.CloseableChannel α
  closed : IO.Ref Bool

def Chan.new : IO (Chan α) := do
  return { ch := ← Std.CloseableChannel.new, closed := ← IO.mkRef false }

/-- Enqueue; `false` if the channel was closed (value dropped). -/
def Chan.send (c : Chan α) (v : α) : IO Bool :=
  c.ch.trySend v

/-- Block until a value arrives or the channel closes (`none`). -/
def Chan.recv (c : Chan α) : IO (Option α) := do
  c.ch.sync.recv

/-- Close: wakes every waiter with `none`; already-queued values stay
readable. Idempotent (the double-close error of the underlying channel is
swallowed). -/
def Chan.close (c : Chan α) : IO Unit := do
  unless ← c.closed.get do
    c.closed.set true
    let _ ← (c.ch.close : EIO Std.CloseableChannel.Error Unit).toIO'

/-- Drain everything currently queued (test inspection helper). -/
partial def Chan.drain (c : Chan α) (acc : List α := []) : IO (List α) := do
  match ← c.ch.tryRecv with
  | none => return acc.reverse
  | some v => Chan.drain c (v :: acc)

/-! ## TaskSet: owned tasks -/

/-- Registry of spawned tasks; the owner joins them all on close. -/
structure TaskSet where
  tasks : Std.Mutex (List (Task (Except IO.Error Unit)))

def TaskSet.new : IO TaskSet := do
  return { tasks := ← Std.Mutex.new [] }

/-- Spawn `act` as a tracked task. -/
def TaskSet.spawn (ts : TaskSet) (act : IO Unit) : IO Unit := do
  let t ← IO.asTask act
  ts.tasks.atomically fun st => do
    let v ← st.get
    st.set (t :: v)

/-- Wait for every tracked task and clear the set. -/
def TaskSet.joinAll (ts : TaskSet) : IO Unit := do
  let all ← ts.tasks.atomically (m := IO) fun st => do
    let v ← st.get
    st.set []
    return v
  for t in all do
    let _ ← IO.wait t

/-! ## Mutex-guarded state -/

/-- A mutex-guarded cell: the atomic read-modify-write the old polling
code did with plain (racy) `IO.Ref` get/set pairs. -/
def OnceRef (α : Type) := Std.Mutex α

def OnceRef.new (a : α) : IO (OnceRef α) :=
  Std.Mutex.new a

/-- Atomic read. -/
def OnceRef.get (r : OnceRef α) : IO α :=
  r.atomically fun st => st.get

/-- Atomic write. -/
def OnceRef.set (r : OnceRef α) (v : α) : IO Unit :=
  r.atomically fun st => st.set v

/-- Atomic read-modify-write; returns what the function returned. -/
def OnceRef.update (r : OnceRef α) (f : α → α × β) : IO β :=
  r.atomically fun st => do
    let (v, b) := f (← st.get)
    st.set v
    return b

end LeanP2P
