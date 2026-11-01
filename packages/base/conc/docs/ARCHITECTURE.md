# leanp2p conc: architecture

`base/conc` holds the concurrency primitives of the stack. Every
package above it gets its tasks, channels, and deadlines from here. The
package knows no wire format, and it imports no other group (ARCHITECTURE §2). It
owns the three concurrency rules that every package above must keep
(ARCHITECTURE §4.1), and it owns the `Clock` seam type (ARCHITECTURE
§3.1).

## Modules

| Module | Holds, and why |
|---|---|
| `Conc.lean` | the root module; one import line per public submodule |
| `Conc/Wrap.lean` | the only module that imports `Std.Sync` and `Std.Async`; it wraps `Std.CloseableChannel`, `Std.Async.Selectable`, and `Std.Async.Selector.sleep`, so a toolchain API move touches one module (ARCHITECTURE §4.1) |
| `Conc/Constants.lean` | `maxTaskErrors`, the one constant of the package (ARCHITECTURE §3.8) |
| `Conc/Error.lean` | `Conc.Error`, the one error inductive of the package (ARCHITECTURE §3.5): `closed` for a send into a closed channel, `deadlineExpired` for `withinDeadline` |
| `Conc/Chan.lean` | `Chan` (new/send/recv/close/drain), the closeable FIFO with a capacity; `Chan.newUnbounded` is the named exception (ARCHITECTURE §4.1; §9, delta 1) |
| `Conc/Select.lean` | `select`, which waits for the first of several parks; it replaces every hand-rolled first-of loop (ARCHITECTURE §4.1; §9, delta 5) |
| `Conc/Pipe.lean` | `Pipe`, a byte queue over a bounded `Chan` |
| `Conc/TaskSet.lean` | `TaskSet` (new/spawn/joinAll); task errors surface to the owner |
| `Conc/OnceRef.lean` | `OnceRef` (new/get/set/update); `update` is the atomic read-modify-write |
| `Conc/Deadline.lean` | `withinDeadline`; on expiry it closes what the work parks on (ARCHITECTURE §4.1; §5.4) |
| `Conc/Clock.lean` | the `Clock` seam, with the production value and the test value that the test advances |
| `Conc/Alarm.lean` | `Alarm`, the task that sleeps on a `Clock` until the due time a loop asked for last (ARCHITECTURE §3.3) |
| `Conc/Outcome.lean` | `Outcome`, the answer and the first fault of a session, with the rule that records no fault after the end (ARCHITECTURE §3.5) |

All declarations live in the `Conc` namespace. The root module
re-exports the public submodules.

The spike module `Conc.lean` is the reference (ARCHITECTURE §10,
row 1). The spike defines `Pipe` in `Conn/Mux.lean` and
`withinDeadline` in `Conn/Upgrade.lean`, and both move here. The root
docs win where they differ: the spike channel is unbounded, and the
spike has no `select` (ARCHITECTURE §9, deltas 1 and 5).

## Public surface

The names are the root names (ARCHITECTURE §4.1 and §7, step 1).

Every operation that can park runs in `Conc.Async`, the `Async` monad
of `Std` (Decisions, "Parks hold no thread"). `Async.run` enters it at
the program edge.

- `Chan` is a closeable FIFO with a capacity of at least 1: `new`,
  `send`, `recv`, `close`, `drain`. `drain` empties the queue and
  returns the queued values. `close` broadcasts EOF: queued values stay
  readable, later receives return `none`, and every parked send wakes
  with `.error .closed`. `close` is idempotent. The one unbounded
  constructor, `Chan.newUnbounded`, carries its reason in the
  docstring. `trySend`, `tryRecv`, and `isClosed` never park. A test
  reads a full or an empty channel through them.
- `select` waits for the first of several parks to complete. A `Park`
  is a receive on a `Chan` or a timer, and `Park.map` maps its result.
  `Park.sleep` fixes its due time at the call, so a `select` that
  loses does not restart it. `select` takes a proof that the array is
  not empty.
- `Pipe` is a byte queue over a bounded `Chan`: `new`, `write`, `read`,
  `close`. The bound counts chunks, so the caller bounds the chunk size.
- `TaskSet.new`, `spawn`, `joinAll`. The owner joins every task, and
  `joinAll` reports task errors to the owner. It throws the error of
  one failed task. For several, it throws one error that counts them
  all and names the first `maxTaskErrors` in the order they ended. A
  join empties the report, and the set stays usable.
- `OnceRef.new`, `get`, `set`, `update`. `update` is the atomic
  read-modify-write, so a shared cell changes in one step
  (ARCHITECTURE §3.8). `updateGet` is the same step with a returned
  value. `set` writes through the same step (Decisions, "`OnceRef.set`
  goes through `modify`").
- `withinDeadline` is a `select` over the work and a timer. On expiry
  it runs `onExpiry : BaseIO Unit`, which closes what the work parks
  on, so the work ends on its own (ARCHITECTURE §4.1; §5.4). `BaseIO`
  keeps `onExpiry` from throwing before the work wakes. A work that has
  ended when the timer fires keeps its value, and a throw from the
  `select` still wakes and joins the work. A work can also end with a
  value after the timer won. No caller sees that value, so
  `withinDeadline` gives it to `release : α → BaseIO Unit` after the
  join. `release` frees a value that holds a resource, such as a
  connection. The default `release` drops the value.
- `Clock` is a seam with the two values of ARCHITECTURE §3.1. A timer
  of `Clock.after` counts from the call. The production value,
  `Clock.system`, reads the system time. The test advances the test
  value, `TestClock.clock`, with `TestClock.advance`. A test timer is
  a channel that `advance` closes when the timer becomes due, so a
  close wakes its park. `TestClock.nextTimer` waits until the code under
  test arms a timer, so a test never advances the time ahead of it.
  `TestClock.close` fires every pending timer and ends every
  `nextTimer`, so no park on the clock outlives its test.
- `Alarm.new`, `set`, `close`, `run`. A loop calls `set` with the due
  time its core asked for, and `set` never parks. A later `set`
  replaces the due time. `run` sleeps on a `Clock` until that time,
  then calls its `fire` argument. `close` wakes and ends it, and so
  does an `.error` from `fire`.
- `Outcome.new`, `recordFault`, `recordWriteFault`, `writeFault`,
  `markClosing`, `finish`, `answer`. The tasks of a session record the
  first fault, unless the session has ended: the loop has answered, or
  the owner has closed it. `answer` gives the owner the loop's answer,
  and throws the fault under an orderly answer (ARCHITECTURE §3.5). A
  shell that reports a failed write in its own way records it with
  `recordWriteFault`, and reads it with `writeFault`.

## Owned contracts

The package owns the three rules of ARCHITECTURE §4.1:

1. **Never cancel; wake by close.** The runtime drops cancelled
   promises, so a cancel strands parked tasks. Every park in the
   package names, in a comment, the close that wakes it
   (PRINCIPLES 3.1).
2. **Every task has an owner that joins it.** `TaskSet` is that owner.
   The owner joins on close, inside the shutdown order of
   ARCHITECTURE §5.5 (PRINCIPLES 3.2).
3. **Shared state is atomic.** Callers change a shared cell through
   `OnceRef.update`, and never get and then set a bare `IO.Ref`
   (PRINCIPLES 3.3).

The package also owns the three things the spike missed
(ARCHITECTURE §4.1):

- Every `Chan` has a capacity. An unbounded channel is a named
  exception, with its reason in the docstring.
- `select` replaces every hand-rolled first-of loop in the stack.
- `joinAll` reports task errors to the owner. A swallowed error hides
  a failed subsystem from the shutdown path. The count of failures is
  exact, and the text of the failures stops at `maxTaskErrors`.

## What the proofs cover

The rules with no IO in them are pure functions, and the IO path calls
them, so the theorems cover the code that runs (ARCHITECTURE §6,
layer 1):

| Function | Theorems |
|---|---|
| `Race.settle` (`Conc/Deadline.lean`) | The work wins a tie. A finished race stays finished. The deadline expires only when the timer won and no answer waits. |
| `takeDue` (`Conc/Clock.lean`) | No test timer fires early. Every due timer leaves the list. The split loses no timer and adds none. |
| `Alarm.clearDue` | A wake clears the time it served. A different time from a later `set` survives. |
| `Outcome.record` | An ended session records nothing, for a fault and for a failed write. The cell keeps the first fault of any list. |
| `TaskSet.Tally` (`Conc/TaskSet.lean`) | A task that starts and ends leaves the live count as it was. Every failure counts. The kept errors never pass `maxTaskErrors`, and a later failure never removes one. `take` gives no report while a task is live, and it gives every kept error once none is. |
| `Outcome.joinAnswer` | A fault under an orderly answer throws. A protocol error stays the answer. With no fault, the answer is the answer of the loop. |

`select` takes a proof that its array is not empty, and `Chan.new`
takes a proof that its capacity is not 0 (ARCHITECTURE §3.7). The
channels and the parks wrap `Std`, so
the suite pins their behavior (CLAUDE.md, "Proofs and tests"). No
theorem covers the wake protocol of `Chan`.

## Decisions

- **Bounded by default.** An unbounded queue converts a peer's send
  rate into our memory (PRINCIPLES 3.4). The loop of ARCHITECTURE §3.3
  needs the bound for back-pressure. A full channel parks the reader,
  and the TCP window carries the pressure to the peer. The gossipsub
  queues need bounded channels too (ARCHITECTURE §7, step 1).
- **Never cancel.** Cancellation drops the promise a task parks on,
  and the waiter never wakes. The silent-peer incident hung shutdown
  this way, and the fix added a close that reaches the park
  (PRINCIPLES 3.1).
- **The `Std` wrap.** Lean v4.34 ships the primitives the package
  needs (ARCHITECTURE §4.1). A direct import would spread toolchain
  names across the stack. The wrapper holds them in one module, so an
  API move touches one module.
- **Parks hold no thread.** The parks run in `Async` and resolve as
  promise continuations, so the tasks share Lean's pool, whose size
  `LEAN_NUM_THREADS` fixes. A blocking `IO.wait` on a pool task makes
  the runtime start a replacement worker (ARCHITECTURE §4.1 gives the
  measurement). A parked loop or reader of a host (§3.3) therefore adds
  no thread. Code inside an `Async` task must not block either:
  a blocking call holds a pool worker.
- **A sender never parks inside `Std`.** `Std.CloseableChannel.close`
  wakes the parked receivers only. A sender parked inside `Std` on a
  full channel wakes only when a receive frees a slot, one sender per
  receive, so a closer that stops reading strands it (rule 1). `Chan`
  keeps the values in the `Std` channel and offers them only with
  `trySend`. A refused sender parks as a receiver on a second `Std`
  channel, `room`. A receive signals `room`, and `close` closes it. A
  `Std` close wakes every receiver, so every parked sender wakes. The
  cost: one signal per transfer, an occasional spare wakeup, and no
  strict arrival order among senders. Capacity 0 would need a send to
  meet a receive inside `Std`, so `Chan.new` takes a proof of `0 < capacity`.
- **`OnceRef.set` goes through `modify`.** A bare `IO.Ref.set` can lose
  its value to a concurrent `IO.Ref.get`. On v4.34, a writer that read
  back each value lost 1387 of 199999 writes against three readers.
  Every read in the stack may race a write, so `OnceRef` exposes no
  bare `set` (PRINCIPLES 3.3).
- **A `TaskSet` counts its tasks and keeps none.** The owner joins on
  close (PRINCIPLES 3.2), so a set can live as long as the program. An
  accept loop that spawns per connection (the streams pair, contract 5)
  must not pay for its ended tasks, because a peer that connects again
  and again would then set our memory use (PRINCIPLES 3.4). The set
  therefore holds a `Tally`, and `Wrap.onEnd` records each end in one
  atomic step. The cost: the kept errors follow the order the tasks
  ended in, and `joinAll` names at most `maxTaskErrors` of them. A scan
  for ended tasks does not work: `IO.hasFinished` is an IO call, so it
  cannot run inside `OnceRef.update`, and a `joinAll` during the scan
  would miss the tasks that the scan holds.
- **`Alarm` and `Outcome` live here.** They need only `Chan`, `Clock`,
  and `OnceRef`, and neither one knows a protocol. Every loop of
  ARCHITECTURE §3.3 with timers needs the first, and every session
  needs the second, so each fact has one home (PRINCIPLES 1.5).
- **`Outcome` records no fault after the owner's close** (`Outcome`,
  "The owner's close"). A `close` that shuts the connection at once breaks
  the writes in flight. The owner asked for that end, so it is no
  failure of the session. One `OnceRef` holds the answer, the faults,
  and the mark, so the check of the end and the record of a fault are
  one atomic step (PRINCIPLES 3.3).
- **A timer counts from its creation.** `Std.Async.Selector.sleep`
  starts inside `select` and resets each time a `select` ends without
  it. A park therefore keeps its due time and builds a fresh sleep for
  the time left at each `select`.

## What the package must not depend on

- No import from a group above `base`: no codec, no crypto, no net, no
  libp2p (ARCHITECTURE §2).
- No wire-format knowledge: no multicodec, no framing, no protocol id.
- No import of `Std.Sync` or `Std.Async` outside `Conc/Wrap.lean`. Lean
  imports are transitive, so `import Conc` still brings their names and
  the `Conc.Wrap` names into scope. A caller names only `Conc` types,
  and no lint checks that.
