import LeanP2P.Crypto.Bytes
import LeanP2P.Net.Transport
/-!
# Streams

The unit of multiplexed communication, and the boundary over which
application protocols run. Protocol logic only ever sees a `Stream`.
-/

namespace LeanP2P

structure Stream where
  read : IO (Option ByteArray)
  write : ByteArray → IO Unit
  close : IO Unit
  reset : IO Unit

/-- A `Connection`-shaped view of a stream (for the buffered reader and
anything else speaking the transport interface over a stream). -/
def Stream.conn (s : Stream) : Connection where
  read := s.read
  write := s.write
  close := s.close
  localAddr := { components := [] }
  remoteAddr := { components := [] }

def Stream.writeLine (s : Stream) (l : String) : IO Unit :=
  s.write ((l.toUTF8).push 10)

/-- Read one LF-terminated line. Spike assumption: writers emit whole lines. -/
partial def Stream.readLine (s : Stream) : IO (Option String) := do
  let rec loop (acc : ByteArray) : IO (Option String) := do
    match acc.toList.findIdx? (· == 10) with
    | some i => return Bytes.toString? (acc.extract 0 i)
    | none =>
      match ← s.read with
      | none => if acc.isEmpty then return none else return Bytes.toString? acc
      | some chunk => loop (acc ++ chunk)
  loop ByteArray.empty

end LeanP2P
