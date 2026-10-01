import LeanP2P.Net.Transport
import LeanP2P.Conn.Mux
import LeanP2P.Conc
/-!
# Simulated network

Deterministic in-memory transport: listeners register under a Multiaddr,
dialing splices two byte streams together. This is the spike's test
harness — the whole stack (security, mux, protocols) runs over it.

The connections are byte streams in the transport sense: a `read` returns
whatever bytes are currently buffered (which may split or coalesce
writes), never losing any. For conformance tests, `Connection.byteSplitting`
wraps a connection so every write is delivered one byte at a time.

Phase 4: the pipes and the accept queue are promise-blocking channels
(step 22); no polling anywhere.
-/

namespace LeanP2P

/-- A byte-stream buffer with EOF, backed by a `Chan` (blocking receive,
no polling). Each `write` becomes one message; `read` returns one message
or `none` on EOF. -/
structure BytePipe where
  ch : Chan ByteArray

def BytePipe.new : IO BytePipe := do
  return { ch := ← Chan.new }

/-- One buffered write (possibly a prefix of the logical stream); `none`
only after EOF with an empty buffer. -/
def BytePipe.read (p : BytePipe) : IO (Option ByteArray) :=
  p.ch.recv

def BytePipe.write (p : BytePipe) (b : ByteArray) : IO Unit := do
  discard <| p.ch.send b

/-- Every byte currently queued (test inspection helper). -/
def BytePipe.peek (p : BytePipe) : IO ByteArray :=
  (·.foldl (· ++ ·) ByteArray.empty) <$> p.ch.drain

def BytePipe.close (p : BytePipe) : IO Unit :=
  p.ch.close

/-- A `Connection`-shaped view of one direction of a splice. -/
def BytePipe.conn (read : BytePipe) (write : BytePipe) (addr : Multiaddr) :
    Connection where
  read := read.read
  write := write.write
  close := do read.close; write.close
  localAddr := { components := [] }
  remoteAddr := addr

/-- Listener internals, kept reachable so `dial` can deliver connections. -/
structure SimListener where
  addr : Multiaddr
  queue : Chan Connection

structure SimNet where
  listeners : OnceRef (List (Multiaddr × SimListener))

def SimNet.new : IO SimNet := do
  return { listeners := ← OnceRef.new [] }

/-- Blocks until a dialed connection arrives or the listener closes. -/
def SimNet.acceptLoop (sl : SimListener) : IO (Option Connection) :=
  sl.queue.recv

/-- Splice two byte pipes into a bidirectional connection pair. -/
def SimNet.splice (c2s s2c : BytePipe) (addr : Multiaddr) : Connection × Connection :=
  let client : Connection :=
    { read := s2c.read, write := c2s.write,
      close := do c2s.close; s2c.close
      localAddr := { components := [] }, remoteAddr := addr }
  let server : Connection :=
    { read := c2s.read, write := s2c.write,
      close := do c2s.close; s2c.close
      localAddr := addr, remoteAddr := { components := [] } }
  (client, server)

def SimNet.listen (net : SimNet) (addr : Multiaddr) : IO (Option Listener) := do
  let sl : SimListener := { addr := addr, queue := ← Chan.new }
  let placed ← net.listeners.update fun ls =>
    if ls.any (·.1 == addr) then (ls, false) else (ls ++ [(addr, sl)], true)
  if placed then
    return (some { addr := addr, accept := SimNet.acceptLoop sl
                   close := sl.queue.close })
  else
    return none

def SimNet.dial (net : SimNet) (addr : Multiaddr) : IO (Option Connection) := do
  match (← net.listeners.get).lookup addr with
  | none => return none
  | some sl => do
    let c2s ← BytePipe.new
    let s2c ← BytePipe.new
    let (client, server) := SimNet.splice c2s s2c addr
    -- `send` is `false` (and the connection dropped) once the listener closed
    if ← sl.queue.send server then return (some client) else return none

/-- The sim network as a first-class transport. -/
def SimNet.transport (net : SimNet) : Transport where
  name := "sim"
  dial := net.dial
  listen := net.listen

/-- A connection whose every write is split into single bytes (the
"hostile transport" of the multistream/noise/yamux conformance tests). -/
def Connection.byteSplitting (c : Connection) : Connection where
  read := c.read
  write := fun b => b.toList.foldlM (fun _ byte => c.write (ByteArray.mk #[byte])) ()
  close := c.close
  localAddr := c.localAddr
  remoteAddr := c.remoteAddr

end LeanP2P
