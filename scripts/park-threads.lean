import Conc

/-!
# The thread cost of a park

This script measures the figures of ARCHITECTURE §4.1: the OS threads that 5000
parked receivers hold, parked by a blocking `IO.wait` on pool tasks and
parked in `Async`. It reads `/proc/self/status`, so it needs Linux.

```
lake env lean --run scripts/park-threads.lean parked
lake env lean --run scripts/park-threads.lean blocking
```

The blocking run starts about 5000 threads for a few seconds.
-/

set_option autoImplicit false

open Conc

/-- The `Threads:` line of `/proc/self/status`. -/
def threads : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  return ((s.splitOn "\n").find? (·.startsWith "Threads:")).getD "?"

/-- The number of parked receivers. -/
def receivers : Nat := 5000

/-- The time the receivers get to park before the count, in ms. -/
def settleMs : Nat := 3000

/-- Park each receiver in a blocking `IO.wait` on a pool task. -/
def blocking : IO Unit := do
  let p : IO.Promise Unit ← IO.Promise.new
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for _ in [0:receivers] do
    tasks := tasks.push (← IO.asTask (do let _ ← IO.wait p.result?; pure ()))
  IO.sleep settleMs.toUInt32
  IO.println s!"blocking IO.wait: {← threads}"
  p.resolve ()
  for t in tasks do discard <| IO.wait t

/-- Park each receiver in `Async`, on a `Chan` receive. -/
def parked : IO Unit := Async.run do
  let c : Chan Unit ← Chan.new 1
  let ts ← TaskSet.new
  for _ in [0:receivers] do
    ts.spawn (discard c.recv)
  let settle ← Park.sleep settleMs ()
  select #[settle]
  let count ← (threads : IO String)
  IO.println s!"parked in Async: {count}"
  c.close
  ts.joinAll

def main (args : List String) : IO Unit := do
  IO.println s!"start: {← threads}"
  if args == ["blocking"] then blocking else parked
