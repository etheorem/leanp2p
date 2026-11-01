import Std.Sync.Channel
import Std.Async.Select
import Std.Async.Timer

/-!
# The `Std` wrapper

The one module of the stack that imports `Std.Sync` and `Std.Async`,
apart from `Std.Async.TCP` in `net/streams` (ARCHITECTURE §4.1 and §9,
delta 7). Lean v4.34 ships the primitives that `conc` needs:
`Std.CloseableChannel` with a capacity, `Std.Async.Selectable`, and
`Std.Async.Selector.sleep`. This module puts each one behind a name of
its own, so a toolchain API move touches this module and no other
(ARCHITECTURE §4.1).

## Parks hold no thread

Every `conc` operation that can park runs in `Conc.Async`, the `Async`
monad of `Std`. A parked `Async` computation is a continuation on a
promise, and it holds no OS thread. The tasks run on Lean's shared pool,
whose size `LEAN_NUM_THREADS` fixes. A blocking wait (`IO.wait`) on a
pool task makes the runtime start a replacement worker instead
(ARCHITECTURE §4.1 gives the measurement). Only `Async.run`, at the
program edge, blocks a thread.

## Answers

The wrapper turns the `Std` error returns into the answers that `conc`
needs. `Std` reports a second close as `.alreadyClosed`. The wrapper
answers `false`, so `Chan.close` can be idempotent.

The wrapper offers no parking send on purpose. A sender parked inside
`Std` on a full channel does not wake on close, so `Chan` sends with
`trySend` only and parks on a channel of its own (`Conc.Chan`, "Why a
sender never parks inside `Std`").
-/

set_option autoImplicit false

namespace Conc

/-- The monad of every `conc` operation that can park. -/
abbrev Async := Std.Async.Async

/-- Run an `Async` computation at the program edge, and block the
calling thread until it ends. `main` and the test runner call it. Code
inside the stack never does. -/
def Async.run {α : Type} (x : Async α) : IO α :=
  x.block

namespace Wrap

open Std.Async in
/-- Wait for a task without holding a thread. -/
def await {α : Type} (t : Task α) : Async α :=
  MonadAwait.await t

/-- Start an `Async` computation as a task on the shared pool. The
task's answer carries the error the computation throws. -/
def spawn {α : Type} (x : Async α) : BaseIO (Task (Except IO.Error α)) := do
  match ← x.asTask.toBaseIO with
  | .ok t => return t.run
  | .error e => return .pure (.error e)

/-- Run `f` on the answer of `t` when `t` ends, or now when `t` has
ended. The call never parks. No owner joins `f`, so `f` must not park,
and it must be one short step. -/
def onEnd {α : Type} (t : Task α) (f : α → BaseIO Unit) : BaseIO Unit :=
  BaseIO.chainTask t f (sync := true)

/-- A closeable channel of `Std`. The other modules of `conc` see only
this name. -/
structure RawChan (α : Type) where
  private ch : Std.CloseableChannel α

namespace RawChan

variable {α : Type}

/-- A channel with the capacity that `Std` takes: `none` is unbounded,
`some 0` is a rendezvous, and `some n` buffers `n` values. -/
def new (capacity : Option Nat) : BaseIO (RawChan α) :=
  return ⟨← Std.CloseableChannel.new capacity⟩

/-- Send the value only when the channel takes it now, without a park:
`true` when it does, `false` when the buffer is full or the channel is
closed. -/
def trySend (c : RawChan α) (v : α) : BaseIO Bool :=
  c.ch.trySend v

/-- Close the channel. `true` on the first close, `false` after. -/
def close (c : RawChan α) : BaseIO Bool := do
  match ← c.ch.close.toBaseIO with
  | .ok () => return true
  | .error _ => return false

/-- True when the channel is closed. -/
def isClosed (c : RawChan α) : BaseIO Bool :=
  c.ch.isClosed

/-- A task that resolves to the next value, or to `none` once the
channel is closed and empty. -/
def recv (c : RawChan α) : BaseIO (Task (Option α)) :=
  c.ch.recv

/-- The next value when one is ready now. `none` when the queue is
empty, closed or not. -/
def tryRecv (c : RawChan α) : BaseIO (Option α) :=
  c.ch.tryRecv

end RawChan

/-- One event source for `selectOne`, as the action that builds its
`Std` selector when the `select` starts.

A `Std.Async.Selectable` hides the type of its event in a field, so it
lives in `Type 1`, and `IO` cannot return it. `Selectable.combine` turns
a selectable into a `Selector α`, which lives in `Type`. A park stores
the action that runs `combine`, and `selectOne` runs it.

The selector answers `Option α`: `some` is the park's result, and
`none` is a wake that does not count, which `selectOne` answers by
selecting again. Only a sleep that fires before its due time answers
`none`. -/
structure RawPark (α : Type) where
  private make : Async (Std.Async.Selector (Option α))

/-- The selector of one selectable. -/
private def single {α β : Type} (s : Std.Async.Selector β) (k : β → Option α) :
    IO (Std.Async.Selector (Option α)) :=
  Std.Async.Selectable.combine #[.case s fun b => pure (k b)]

/-- The park on the next receive of a channel. `k` maps the received
value, or `none` for a closed and empty channel. `onValue` runs once
the park has taken a value, so `Chan` can signal the freed slot. -/
def RawPark.recv {α β : Type} (c : RawChan β) (onValue : BaseIO Unit)
    (k : Option β → α) : RawPark α :=
  ⟨Std.Async.Selectable.combine #[.case c.ch.recvSelector fun o => do
    if o.isSome then onValue
    pure (some (k o))]⟩

/-- The park on the monotonic time `dueMs` (`IO.monoMsNow`).

`Std.Async.Selector.sleep` starts its timer inside `select` and resets
it when a `select` ends without it, so a sleep of a fixed length counts
from each `select`. The park therefore keeps the due time and builds a
fresh sleep for the time left each time a `select` starts. A loop that
keeps selecting on the park still fires at `dueMs`.

libuv counts a new timer from its cached loop time, which can trail
`IO.monoMsNow` by the time the loop has run since its last update. A
fresh sleep can therefore end a few milliseconds before `dueMs`. The
park reads the clock when the sleep ends and answers `none` while
`dueMs` is still ahead, so `selectOne` arms a sleep for the rest. -/
def RawPark.sleepUntil {α : Type} (dueMs : Nat) (k : α) : RawPark α :=
  ⟨do
    let left := dueMs - (← IO.monoMsNow)
    let s ← Std.Async.Selector.sleep (Std.Time.Millisecond.Offset.ofNat left)
    Std.Async.Selectable.combine #[.case s fun () => do
      return if (← IO.monoMsNow) ≥ dueMs then some k else none]⟩

/-- Map the result of a park. -/
def RawPark.map {α β : Type} (f : α → β) (p : RawPark α) : RawPark β :=
  ⟨do single (← p.make) (·.map f)⟩

/-- Wait for the first park that completes, and return its mapped
result. `Std` polls the parks in a random order, so no park starves the
others. `Std` throws on an empty array, and `Conc.select` rules that
array out with a proof.

A wake that does not count (a sleep that ended early, see
`RawPark.sleepUntil`) starts the `select` again with fresh selectors.
The function is `partial`: it ends when a park completes, and no
measure shows that a park ever does, the standing case of the IO loops
(CLAUDE.md, "`partial def`"). -/
partial def selectOne {α : Type} (parks : Array (RawPark α)) : Async α := do
  let sels ← parks.mapM (·.make)
  -- Park: a receive park wakes by a send or a close of its channel, and
  -- a sleep park wakes when its `Std` timer ends.
  match ← Std.Async.Selectable.one (sels.map fun s => .case s pure) with
  | some a => return a
  | none => selectOne parks

end Wrap

end Conc
