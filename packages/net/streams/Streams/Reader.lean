import Conc
import Streams.Conn

/-!
# The reader task of a session

A session of ARCHITECTURE §3.3 has one reader task. It turns each
connection read into an event for the loop, and the end of the
connection into a last event. The yamux, mplex, and Noise shells run
the same task, so it lives here, beside `Connection` (§3.8). Each shell
supplies its own posts, since each has its own `Event` type.

The reader takes a credit before each read. The loop hands the credits
back on its own terms, so the reader reads ahead of the loop by the
credits it holds, and the rest of the peer's bytes stay in the
connection, where TCP slows the peer (§5.1).
-/

set_option autoImplicit false

namespace Streams

open Conc

/-- The reader task over `conn`. Before each read it takes a credit
from `credits`. It posts each chunk with `post`, and the end of the
connection with `postEnd`. A failed read reaches `onFault` and then
ends the reads like the end of the connection. The task ends when the
credits close, when a post answers `.error` (the loop has ended), or at
the end of the connection. -/
def readLoop (conn : Connection) (credits : Chan Unit) (onFault : IO.Error → BaseIO Unit)
    (post : ByteArray → Async (Except Conc.Error Unit)) (postEnd : Async Unit) : Async Unit := do
  repeat
    -- Park: the loop returns a credit, and the teardown closes the
    -- credits.
    if (← credits.recv).isNone then break
    -- Park: the peer's bytes wake it, and so does the close of the
    -- connection.
    let chunk ← try conn.read catch e => do onFault e; pure none
    match chunk with
    | some b =>
      if let .error _ ← post b then break
    | none =>
      postEnd
      break

end Streams
