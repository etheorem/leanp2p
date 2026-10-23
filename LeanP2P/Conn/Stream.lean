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

/-- A stream whose reads start with `first` and then continue on `s`.
This is how bytes a negotiation stage over-read (they sit in its
`BufReader`) reach the application: a handler building its own reader
over the stream picks them up through `read` instead of losing them.
`first` is handed out exactly once. -/
def Stream.prependBytes (s : Stream) (first : ByteArray) : IO Stream := do
  if first.isEmpty then pure s
  else do
    let pending ← IO.mkRef true
    pure { s with
      read := do
        if ← pending.get then do
          pending.set false
          pure (some first)
        else s.read }

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
