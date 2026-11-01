# leanp2p conc: plan

This plan refines the root `docs/PLAN.md` for `base/conc`. The root
plan owns the order across packages (PLAN.md, "How to read this
plan"). Unit 1 below is the root unit W1.1. Its done-when is the root
row plus the root definition of done. In short: the surface follows
ARCHITECTURE §4.1, the contracts hold, the carried tests pass, the
suite passes under `+RTS -N1`, and the import lint is green.

## Units

| Unit | Root deps | Deliverable | Done when |
|---|---|---|---|
| 0 | none | this documentation pair, the first work unit of the package (ARCHITECTURE §2) | written, and consistent with the root docs |
| 1 | W0 | the primitives of ARCHITECTURE §4.1: bounded `Chan`, `select`, `Pipe`, `TaskSet`, `OnceRef`, `withinDeadline`, the `Clock` seam, `Alarm`, `Outcome`, and the `Std.Sync`/`Std.Async` wrapper | the root W1.1 row holds: the primitives exist, the contracts hold, and the suite passes under `+RTS -N1` |

Unit 0 is done. Unit 1 is the only implementation unit of the
package.

## Test milestones (unit 1)

Behavior tests and the theorems of the package ARCHITECTURE ("What the
proofs cover") close unit 1. The package has no wire vectors: the vector
infrastructure of root W0.3 does not concern `base/conc`. The suite follows the root test-runner layout of W0.2,
and the `-N1` pass is required.

- A parked `recv` wakes when another task closes the channel, and it
  returns `none` after the queued values drain.
- A second `close` is a no-op.
- Send three values, close, then receive the three values in send
  order and then `none` (drain, then EOF).
- `send` into a full channel parks until a receive frees a slot
  (capacity back-pressure).
- `close` alone wakes every parked `send` with `.error .closed`, and
  no refused value enters the queue.
- `select` over two parked receives takes the park that completes
  first, in both orders.
- A spawned task that fails hands the error to the owner at
  `joinAll`.
- `joinAll` on a set with one live task returns only after that task
  ends. It joins a task that a task of the set spawns during the join,
  and two joins of one set both return.
- Past `maxTaskErrors` failures, `joinAll` counts every failure and
  names only the kept ones. A join reports an error once, and the set
  runs new tasks after it.
- N tasks update one `OnceRef` M times each; the cell holds N×M
  updates, with none lost.
- A `set` survives concurrent `get`s.
- 2000 tasks parked on one channel hold no thread, and one close wakes
  them all.
- `withinDeadline` closes what the work parks on, and the work ends on
  its own. A value that the work returns after the expiry goes to
  `release`. A tied race answers with the value or the expiry, never
  both.
- The test `Clock` advances by the step the test gives. A timer on
  that clock fires at the advanced time.
- `Alarm` fires at the due time, a later `set` replaces the due time,
  and `close` or an `.error` from `fire` ends `run`.
- `Outcome` keeps the first fault and records none after the end. A
  fault under an orderly answer throws, and a protocol error stays the
  answer.
