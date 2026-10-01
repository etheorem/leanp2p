import LeanP2P.Net.Transport
import LeanP2P.Crypto.Bytes
/-!
# Buffered byte reader

Real transports return arbitrary prefixes on `read` - message boundaries
must be reconstructed on top. `BufReader` wraps a `Connection` with an
internal buffer: bytes over-read by one framing layer stay available to the
next, and no data is ever lost between calls.
-/

namespace LeanP2P

structure BufReader where
  conn : Connection
  buf : IO.Ref ByteArray

def BufReader.ofConn (c : Connection) : IO BufReader := do
  return { conn := c, buf := ← IO.mkRef ByteArray.empty }

/-- Exactly `n` bytes, or `none` on EOF. The internal buffer is drained
up front (taken bytes must not be handed out twice: with a leftover ≥ n
the old code returned the buffered bytes *and* left them buffered, so
every later read was shifted - latent until phase 5's large flow-controlled
records made leftovers the norm). -/
partial def BufReader.readExactly (r : BufReader) (n : Nat) :
    IO (Option ByteArray) := do
  let first ← r.buf.get
  r.buf.set ByteArray.empty
  let rec loop (acc : ByteArray) : IO (Option ByteArray) := do
    if acc.size ≥ n then
      -- keep the over-read bytes for the next call
      r.buf.set (acc.extract n acc.size)
      return (some (acc.extract 0 n))
    -- buffer already drained: wait for one more chunk
    match ← r.conn.read with
    | none => return none
    | some chunk =>
        if chunk.size = 0 then loop acc else loop (acc ++ chunk)
  loop first

/-- Whatever is buffered right now, otherwise one fresh chunk; `none` on EOF. -/
partial def BufReader.readAvail (r : BufReader) : IO (Option ByteArray) := do
  let b ← r.buf.get
  if b.size > 0 then do
    r.buf.set ByteArray.empty
    return (some b)
  r.conn.read

end LeanP2P
