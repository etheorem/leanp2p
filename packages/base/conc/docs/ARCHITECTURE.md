# leanp2p conc: architecture

`base/conc` is the concurrency floor of the stack. Every package above
it gets its tasks, channels, and deadlines from here. The package knows
no wire format, and it imports no other group (ARCHITECTURE §2). It
owns the three concurrency rules that every package above must keep
(ARCHITECTURE §4.1), and it owns the `Clock` seam type (ARCHITECTURE
§3.1).

## Modules

| Module | Holds, and why |
|---|---|
| `Conc.lean` | the root module; one import line per public submodule |
| `Conc/Wrap.lean` | the only module that imports `Std.Sync` and `Std.Async`; it wraps `Std.Sync.CloseableChannel`, `Std.Async.Selectable`, and `Std.Async.Selector.sleep`, so a toolchain API move touches one module (ARCHITECTURE §4.1) |
| `Conc/Chan.lean` | `Chan` (new/send/recv/close/drain), the closeable FIFO with a capacity; `Chan.newUnbounded` is the named exception (ARCHITECTURE §4.1; §9, delta 1) |
| `Conc/Select.lean` | `select`, which waits for the first of several parks; it replaces every hand-rolled first-of loop (ARCHITECTURE §4.1; §9, delta 5) |
| `Conc/Pipe.lean` | `Pipe`, a byte queue over a bounded `Chan` |
| `Conc/TaskSet.lean` | `TaskSet` (new/spawn/joinAll); task errors surface to the owner |
| `Conc/OnceRef.lean` | `OnceRef` (new/get/set/update); `update` is the atomic read-modify-write |
| `Conc/Deadline.lean` | `withinDeadline`; on expiry it closes what the work parks on (ARCHITECTURE §5.4) |
| `Conc/Clock.lean` | the `Clock` seam, with the production value and the test value that the test advances |

All declarations live in the `Conc` namespace. The root module
re-exports the public submodules.

The spike module `Conc.lean` is the reference (ARCHITECTURE §10,
row 1). The spike defines `Pipe` in `Conn/Mux.lean` and
`withinDeadline` in `Conn/Upgrade.lean`, and both move here. The root
docs win where they differ: the spike channel is unbounded, and the
spike has no `select` (ARCHITECTURE §9, deltas 1 and 5).

## Public surface

The names are the root names (ARCHITECTURE §4.1 and §7, step 1).

- `Chan` is a closeable FIFO with a capacity: `new`, `send`, `recv`,
  `close`, `drain`. `drain` empties the queue and returns the queued
  values. `close` broadcasts EOF: queued values stay readable, and
  later receives return `none`. `close` is idempotent. The one
  unbounded constructor, `Chan.newUnbounded`, carries its reason in
  the docstring.
- `select` waits for the first of several parks to complete.
- `Pipe` is a byte queue over a bounded `Chan`.
- `TaskSet.new`, `spawn`, `joinAll`. The owner joins every task, and
  `joinAll` reports task errors to the owner.
- `OnceRef.new`, `get`, `set`, `update`. `update` is the atomic
  read-modify-write, so a shared cell changes in one step
  (ARCHITECTURE §3.8).
- `withinDeadline` is a `select` over the work and a timer. On expiry
  it closes what the work parks on, so the work ends on its own
  (ARCHITECTURE §4.1; §5.4).
- `Clock` is a seam with the two values of ARCHITECTURE §3.1. The
  production value reads the system time; the test advances the test
  value.

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
  a failed subsystem from the shutdown path.

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

## What the package must not depend on

- No import from a group above `base`: no codec, no crypto, no net, no
  libp2p (ARCHITECTURE §2).
- No wire-format knowledge: no multicodec, no framing, no protocol id.
- No import of `Std.Sync` or `Std.Async` outside `Conc/Wrap.lean`, and
  no re-export of their names through the root module.
