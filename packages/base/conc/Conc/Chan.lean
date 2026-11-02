import Conc.Wrap
import Conc.Error

/-!
# `Chan`: the closeable FIFO

A `Chan` is a FIFO with a capacity (ARCHITECTURE §4.1). It holds the
three rules of the stack at the smallest scale:

* **Bounded.** A full channel parks the sender. That park carries
  back-pressure up to the producer, and over TCP up to the peer
  (PRINCIPLES 3.4). `Chan.newUnbounded` is the named exception.
* **Close is EOF.** `close` broadcasts the end: queued values stay
  readable, and the receives after them return `none`. Every parked
  receiver and every parked sender wakes on the close. `close` is
  idempotent.
* **Wake by close.** A park ends by a value or by a close (PRINCIPLES
  3.1). Each park below names its close.

The parks run in `Async` (`Conc.Wrap`), so a parked send or receive
holds no thread.

## Why a sender never parks inside `Std`

`Std.CloseableChannel.close` resolves the parked receivers only. A
sender parked inside `Std` on a full channel wakes only when a receive
frees a slot, one sender per receive, so a closer that stops reading
would strand it, against rule 1.

A `Chan` therefore keeps the values in a `Std` channel, and a sender
offers a value only with `trySend`. On a full channel the sender
parks as a *receiver* on `room`, a second `Std` channel of capacity 1,
and a `Std` close wakes every receiver. The signals on `room`:

* A receive that takes a value frees a slot, and it sends a token on
  `room`.
* A send that succeeds sends another token, because the slot that it
  filled may not have been the last free slot.
* `close` closes `room`. Every parked sender wakes, finds the channel
  closed, and answers `.error .closed`.

Every signal sends its token with `trySend`, so a signal never parks.
A token that finds `room` full loses no wakeup. The token already in
`room` wakes the next sender, and that sender sends a token when it
succeeds. A sender that wakes and finds no free slot parks again, so a
spare token costs one extra loop and nothing else. A new sender can take
a free slot before a parked sender wakes, so `Chan` does not serve the
senders in strict arrival order.
-/

set_option autoImplicit false

namespace Conc

/-- A closeable FIFO with a capacity. -/
structure Chan (α : Type) where
  private raw : Wrap.RawChan α
  /-- The signal that a slot may be free (module doc). -/
  private room : Wrap.RawChan Unit

namespace Chan

variable {α : Type}

/-- A channel that buffers `capacity` values. A sender parks while the
buffer is full. The capacity is at least 1, and `decide` proves it for a
literal, so a call reads `Chan.new 16`. Capacity 0 would make a send
meet a receive inside `Std`, where a parked sender cannot wake by close
(module doc). -/
def new (capacity : Nat) (_h : 0 < capacity := by decide) : BaseIO (Chan α) :=
  return ⟨← Wrap.RawChan.new (some capacity), ← Wrap.RawChan.new (some 1)⟩

/-- A channel with no capacity limit. This is the one exception to the
bound (ARCHITECTURE §4.1), and a caller states its reason: the queue
length must have a bound of another kind, for example a fixed number of
producers that each send once. A queue that a peer fills needs `new`. -/
def newUnbounded : BaseIO (Chan α) :=
  return ⟨← Wrap.RawChan.new none, ← Wrap.RawChan.new (some 1)⟩

/-- Signal that a slot may be free. The call never parks. -/
private def signalRoom (c : Chan α) : BaseIO Unit :=
  discard <| c.room.trySend ()

/-- Send a value. The send parks while the buffer is full.
`.error .closed` when the channel is closed at the start of the send, or
closes while the send parks. -/
def send (c : Chan α) (v : α) : Async (Except Error Unit) := do
  repeat
    if ← c.raw.trySend v then
      c.signalRoom
      return .ok ()
    if ← c.raw.isClosed then return .error .closed
    -- Park: a receive that frees a slot sends on `room`, and `close`
    -- closes `room`. A token sent between the refused `trySend` and this
    -- receive waits in `room`, so no wakeup is lost.
    discard <| Wrap.await (← c.room.recv)
  return .error .closed

/-- Send the value only when the channel takes it now. `false` when the
buffer is full or the channel is closed. The call never parks. -/
def trySend (c : Chan α) (v : α) : BaseIO Bool := do
  let sent ← c.raw.trySend v
  if sent then c.signalRoom
  return sent

/-- The next value, in send order. `none` once the channel is closed and
its queue is empty: the end of the stream (§3.5). -/
def recv (c : Chan α) : Async (Option α) := do
  -- Park: a send wakes it, and so does `close`.
  let v ← Wrap.await (← c.raw.recv)
  if v.isSome then c.signalRoom
  return v

/-- The next value when one is ready now. `none` when the queue is
empty. -/
def tryRecv (c : Chan α) : BaseIO (Option α) := do
  let v ← c.raw.tryRecv
  if v.isSome then c.signalRoom
  return v

/-- Close the channel. The queued values stay readable, every parked
receive wakes with `none`, and every parked send wakes with
`.error .closed`. A second close does nothing. -/
def close (c : Chan α) : BaseIO Unit := do
  discard c.raw.close
  discard c.room.close

/-- True when the channel is closed. -/
def isClosed (c : Chan α) : BaseIO Bool :=
  c.raw.isClosed

/-- Empty the queue now, and return the values in send order. The call
never parks. -/
def drain (c : Chan α) : BaseIO (List α) := do
  let mut out : Array α := #[]
  -- The loop ends at the first empty poll. A concurrent sender can
  -- extend it, and the caller closes first when that matters.
  repeat
    match ← c.tryRecv with
    | some v => out := out.push v
    | none => break
  return out.toList

/-- The receive park of `Conc.Select`. It signals `room` after it takes
a value, as `recv` does. -/
def recvPark {β : Type} (c : Chan α) (k : Option α → β) : Wrap.RawPark β :=
  Wrap.RawPark.recv c.raw c.signalRoom k

/-- The usual call: `decide` proves the literal capacity is not 0. -/
example : BaseIO (Chan Nat) := Chan.new 16

end Chan

end Conc
