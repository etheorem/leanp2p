import Streams.Conn

/-!
# `BufReader`: the buffered reader of one stage

A stage that parses a wire format reads more than it needs. A chunk can
end inside the next message, or inside the first message of the next
stage. A `BufReader` holds those bytes between reads.

A reader is a value, with no `IO.Ref` inside. Each read returns the
bytes and the reader that holds the rest, and the stage passes the
reader from read to read. When the stage ends, `leftover` gives the
bytes that it read too far. The next stage builds its own reader from
them with `BufReader.new`. So the types show the hand-over
(ARCHITECTURE §4.7, "No reader strand"), and no two stages share one
reader (§5.6).

A reader value is good for one read. An older value still holds bytes
that a later read consumed, so a stage that uses an old value again
reads those bytes twice.

## Cost

The reader keeps the buffer and a start offset. A read that the buffer
can serve copies the bytes that it returns, and moves the offset. The
rest of the buffer stays in place. So a chunk that holds many small
frames costs one pass over its bytes, for any count of frames. Only
`fill` compacts the buffer, and `fill` runs only when fewer bytes
remain than the read needs.

## Theorems

The offset arithmetic is pure, so its rules are theorems: a new reader
holds its seed, `drop` consumes the bytes it names and no more, and
`peek` copies at most the bytes it names.
-/

set_option autoImplicit false

namespace Streams

open Conc

/-- The buffered reader of one stage over one connection. -/
structure BufReader where
  /-- The connection that the stage reads. -/
  conn : Connection
  /-- The bytes read from `conn`. The bytes before `pos` are consumed. -/
  private buf : ByteArray
  /-- The offset of the first byte that is not consumed. -/
  private pos : Nat

namespace BufReader

/-- A reader over `conn`, with the bytes that the stage before read too
far as its seed (§4.7). -/
def new (conn : Connection) (leftover : ByteArray := .empty) : BufReader :=
  ⟨conn, leftover, 0⟩

/-- The bytes read and not consumed. A stage that ends gives them to the
next stage. -/
def leftover (r : BufReader) : ByteArray :=
  r.buf.extract r.pos r.buf.size

/-- The count of the bytes read and not consumed. -/
def available (r : BufReader) : Nat :=
  r.buf.size - r.pos

/-- The first `k` bytes that are not consumed, or fewer when fewer are
in the buffer. The call reads nothing from the connection, and copies
at most `k` bytes. -/
def peek (r : BufReader) (k : Nat) : ByteArray :=
  r.buf.extract r.pos (r.pos + k)

/-- Read one more chunk into the buffer. `none` at the end of the
stream. The consumed bytes go, so the buffer holds the rest and the new
chunk. -/
def fill (r : BufReader) : Async (Option BufReader) := do
  match ← r.conn.read with
  | some chunk => return some ⟨r.conn, r.leftover ++ chunk, 0⟩
  | none => return none

/-- The bytes in the buffer, or the next chunk when the buffer is empty.
`none` at the end of the stream. -/
def read (r : BufReader) : Async (Option (ByteArray × BufReader)) := do
  if r.available > 0 then return some (r.leftover, ⟨r.conn, .empty, 0⟩)
  match ← r.conn.read with
  | some chunk => return some (chunk, ⟨r.conn, .empty, 0⟩)
  | none => return none

/-- Exactly `n` bytes. `none` when the stream ends first. The caller caps
`n` before the call when `n` comes from the wire (§5.1). -/
def readExactly (r : BufReader) (n : Nat) : Async (Option (ByteArray × BufReader)) := do
  -- The buffer holds the bytes: copy them out, and move the offset.
  if n ≤ r.available then
    return some (r.buf.extract r.pos (r.pos + n), { r with pos := r.pos + n })
  match ← r.conn.readExactly n r.leftover with
  | some (bytes, rest) => return some (bytes, ⟨r.conn, rest, 0⟩)
  | none => return none

/-- Consume the first `k` bytes of the buffer, or every byte of the
buffer when it holds fewer. The framing read calls it after it has
parsed a header out of `peek`. -/
def drop (r : BufReader) (k : Nat) : BufReader :=
  { r with pos := min (r.pos + k) r.buf.size }

/-! ## Theorems -/

/-- A new reader holds its seed, whole. -/
@[simp] theorem leftoverNew (conn : Connection) (seed : ByteArray) :
    (new conn seed).leftover = seed := by
  simp [new, leftover]

/-- A new reader has its seed available. -/
@[simp] theorem availableNew (conn : Connection) (seed : ByteArray) :
    (new conn seed).available = seed.size := by
  simp [new, available]

/-- The leftover is exactly the available bytes. -/
theorem sizeLeftover (r : BufReader) : r.leftover.size = r.available := by
  simp [leftover, available]

/-- `drop` consumes the bytes that it names, or every byte when fewer
are available. `omega` decides the arithmetic of the `min`. -/
theorem availableDrop (r : BufReader) (k : Nat) :
    (r.drop k).available = r.available - k := by
  simp only [drop, available]
  omega

/-- A drop of no byte changes no count. -/
theorem availableDropZero (r : BufReader) : (r.drop 0).available = r.available := by
  simp [availableDrop]

/-- Two drops consume as one drop of both counts. -/
theorem availableDropDrop (r : BufReader) (j k : Nat) :
    ((r.drop j).drop k).available = (r.drop (j + k)).available := by
  simp only [availableDrop]
  omega

/-- `drop` keeps the connection. -/
@[simp] theorem connDrop (r : BufReader) (k : Nat) : (r.drop k).conn = r.conn := rfl

/-- `peek` copies at most the bytes that it names. -/
theorem sizePeekLe (r : BufReader) (k : Nat) : (r.peek k).size ≤ k := by
  simp only [peek, ByteArray.size_extract]
  omega

/-- `peek` copies at most the bytes that are available. -/
theorem sizePeekLeAvailable (r : BufReader) (k : Nat) :
    (r.peek k).size ≤ r.available := by
  simp only [peek, available, ByteArray.size_extract]
  omega

end BufReader

end Streams
