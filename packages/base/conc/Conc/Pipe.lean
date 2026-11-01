import Conc.Chan

/-!
# `Pipe`: a byte queue

A `Pipe` carries byte chunks from one task to another over a bounded
`Chan` (the package ARCHITECTURE). The bound limits the number of
chunks in flight, so a fast writer parks until the reader catches up.
The bound counts chunks and ignores their size, so the caller bounds the
chunk size (PRINCIPLES 3.4).
An in-memory transport can stand on it: the writer is one side of a
connection, and the reader is the other side.
-/

set_option autoImplicit false

namespace Conc

/-- A byte queue with a bound on the chunks in flight. -/
structure Pipe where
  private chan : Chan ByteArray

namespace Pipe

/-- A pipe that holds up to `capacity` chunks, at least one. -/
def new (capacity : Nat) (h : 0 < capacity := by decide) : BaseIO Pipe :=
  return ⟨← Chan.new capacity h⟩

/-- Write a chunk. The write parks while the pipe is full. A read that
frees a slot wakes it, and so does `close`. The pipe drops an empty
chunk, so a read never returns one. `.error .closed` when the pipe is
closed. -/
def write (p : Pipe) (b : ByteArray) : Async (Except Error Unit) := do
  if !b.isEmpty then return ← p.chan.send b
  -- The empty chunk goes nowhere, but a closed pipe still says so.
  return if ← p.chan.isClosed then .error .closed else .ok ()

/-- The next chunk, in write order. The read parks on an empty pipe. A
write wakes it, and so does `close`. `none` once the pipe is closed and
empty: the end of the stream. -/
def read (p : Pipe) : Async (Option ByteArray) :=
  p.chan.recv

/-- Close the pipe. Queued chunks stay readable. A second close does
nothing. -/
def close (p : Pipe) : BaseIO Unit :=
  p.chan.close

end Pipe

end Conc
