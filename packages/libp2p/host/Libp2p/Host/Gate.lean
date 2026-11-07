import Conc

/-!
# `Gate`: a task group that stops taking tasks

The host owns the tasks of its listeners and its sessions, and it
joins them in the shutdown order (ARCHITECTURE §5.5; PRINCIPLES 3.2).
Some of those tasks start outside any task the host owns: a dial runs
in the caller's task, and its session task starts when the dial ends.
A `Conc.TaskSet` keeps every task spawned before its `joinAll` ends,
but a spawn after that would start a task nobody joins.

A gate closes that window. `close` takes the tasks out and shuts the
gate in one atomic step, and a later `spawn` is refused. The refused
caller wakes the work with the close that reaches its park, then joins
the work in its own task. So every task has an owner that joins it,
before the shutdown or after it.

A task's fault reaches the owner at the join, as `TaskSet.joinAll`
hands it on.
-/

set_option autoImplicit false

namespace Libp2p.Host

open Conc

/-- A task group that refuses new tasks once its owner closes it. -/
structure Gate where
  /-- The tasks; `none` once the gate is closed. -/
  private tasks : OnceRef (Option (Array (Task (Except IO.Error Unit))))

namespace Gate

/-- An open gate with no tasks. -/
def new : BaseIO Gate :=
  return ⟨← OnceRef.new (some #[])⟩

/-- Start `act` as a task of the gate, and answer `true`. When the gate
is closed, run `wake`, which closes what `act` parks on, then join `act`
here, and answer `false`. A fault of `act` then passes to the caller. -/
def spawn (g : Gate) (act : Async Unit) (wake : BaseIO Unit) : Async Bool := do
  -- The ascriptions mark the steps `BaseIO`, so the lift into `Async`
  -- applies (see `Conc.TaskSet.joinAll`).
  if (← (g.tasks.get : BaseIO (Option (Array (Task (Except IO.Error Unit)))))).isNone then
    -- Closed before the start: `act` runs here, after the wake.
    wake
    act
    return false
  let t ← (Wrap.spawn act : BaseIO (Task (Except IO.Error Unit)))
  let kept ← (g.tasks.updateGet fun
    | some ts => (true, some (ts.push t))
    | none => (false, none) : BaseIO Bool)
  if kept then return true
  -- The gate closed after the start, so its `close` did not take the
  -- task. This caller owns it: wake it, and join it.
  wake
  match ← Wrap.await t with
  | .ok () => return false
  | .error e => throw e

/-- Close the gate, and wait for every task it took. Then throw the
first fault in spawn order. A second close waits for nothing. -/
def close (g : Gate) : Async Unit := do
  let ts ← (g.tasks.updateGet fun ts => (ts.getD #[], none) :
    BaseIO (Array (Task (Except IO.Error Unit))))
  let mut errors : Array IO.Error := #[]
  for t in ts do
    -- Park: the task wakes the join when it ends. The shutdown order
    -- closes what each task parks on before this join (§5.5).
    if let .error e ← Wrap.await t then errors := errors.push e
  match errors.toList with
  | [] => return ()
  | [e] => throw e
  | es => throw <| IO.userError s!"{es.length} tasks failed: {es.map toString}"

end Gate

end Libp2p.Host
