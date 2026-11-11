import Streams.Conn

/-!
# The in-memory sim: the test `Transport` value

Every seam has a production value and a test value (ARCHITECTURE §3.1).
The sim is the test value of `Transport`. Every protocol suite above
this package runs on it, and only the transport suite touches real TCP
(PRINCIPLES 1.4).

A `Net` is one simulated network: a registry of listeners by address.
A dial to an address makes two `Pipe`s, one for each direction, and
gives the far end to the listener. Each pipe holds `simPipeChunks`
chunks, so a fast writer parks until the reader reads, as a TCP
window makes it wait.

## The hostile mode

A read can split or join writes (`Connection.read`). A sim that keeps
the write boundaries hides a reader that depends on them. One such
reader once hid a cipher bug per chunk, until TCP joined the bytes
(PRINCIPLES 1.6). With `splitWrites`, every write of the net arrives
one byte at a time, so a boundary bug fails in the sim first.

The reading end does the split. The pipe carries each write whole, and
each read returns one byte of the chunk that the end holds. Only the
first byte of a chunk waits on the pipe. A split at the writing end
would put one byte in each pipe slot, and each byte would then cost a
park, a wake, and a task on the shared pool. Two tasks that hand over
one byte at a time contend on the pool's lock, more so with more
workers.

## Close and teardown

The sim keeps the close rules of a TCP transport (§4.7):

* `close` closes both pipes of the end. The peer reads the queued bytes
  and then EOF, our own parked read wakes with `none`, and a write of
  the peer after the close fails.
* A failed write closes both pipes, and then throws.
* A listener `close` wakes every parked accept, and closes the
  connections that are still in the queue, so their dialers see EOF.

The registry changes through `OnceRef.update`, never through a get and
then a set (PRINCIPLES 3.3).
-/

set_option autoImplicit false

namespace Streams.Sim

open Conc Multiformats

/-- The state of one sim network. -/
private structure Net.State where
  /-- The listeners: a registration number, the address, and the queue
  of dialed connections. -/
  listeners : List (Nat × Multiaddr × Chan Connection)
  /-- The next registration number. -/
  nextListener : Nat
  /-- The next `/memory` port for the address of a dialer's end. -/
  nextPort : Nat

/-- One simulated network. -/
structure Net where
  private state : OnceRef Net.State
  /-- True when every write of the net arrives one byte at a time. -/
  splitWrites : Bool

/-- The fault of a write to a closed sim connection. A sim has no
socket, so the system code is 0. -/
private def closedError : IO.Error :=
  .resourceVanished 0 "sim: the connection is closed"

/-- One byte of the held chunk, and the chunk with its offset moved on.
`none` when the chunk is used up. The offset keeps the rest in place,
so a read copies one byte, whatever the size of the chunk. -/
private def takeByte (held : ByteArray × Nat) : Option ByteArray × (ByteArray × Nat) :=
  let (chunk, pos) := held
  if pos < chunk.size then (some (chunk.extract pos (pos + 1)), (chunk, pos + 1))
  else (none, held)

/-- The split read (module doc, "The hostile mode"): one byte of the
held chunk, or the first byte of the next chunk of the pipe. -/
private def readByte (inbound : Pipe) (held : OnceRef (ByteArray × Nat)) :
    Async (Option ByteArray) := do
  -- The ascription keeps the step `BaseIO`, as in `Net.dial`.
  if let some b ← (held.updateGet takeByte : BaseIO (Option ByteArray)) then
    return some b
  -- Park: the peer's write wakes it, and so does the close of the pipe.
  match ← inbound.read with
  | none => return none
  | some chunk =>
    -- The pipe drops empty chunks, so the chunk has a first byte.
    held.set (chunk, 1)
    return some (chunk.extract 0 1)

/-- One end of a sim connection: it reads `inbound` and writes
`outbound`. -/
private def endpoint (inbound outbound : Pipe) (localAddr remoteAddr : Multiaddr)
    (split : Bool) : BaseIO Connection := do
  let held ← OnceRef.new (ByteArray.empty, 0)
  let shut : BaseIO Unit := do
    outbound.close
    inbound.close
  return {
    read := if split then readByte inbound held else inbound.read
    write := fun b => do
      let sent ← outbound.write b
      if let .error _ := sent then
        -- A failed write tears the connection down before the throw.
        shut
        throw closedError
    close := do shut
    localAddr
    remoteAddr }

namespace Net

/-- An empty network. -/
def new (splitWrites : Bool := false) : BaseIO Net :=
  return ⟨← OnceRef.new { listeners := [], nextListener := 0, nextPort := 0 }, splitWrites⟩

/-- The `/memory/<port>` address of a dialer's end. -/
private def memoryAddr (port : Nat) : Async Multiaddr := do
  match Multiaddr.parse? s!"/memory/{port}" with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"sim: /memory/{port} does not parse"

/-- Dial `addr` on the network. `none` when nothing listens there, or
when the listener closes before it queues the connection. A dial parks
while the queue of the listener is full. -/
def dial (n : Net) (addr : Multiaddr) : Async (Option Connection) := do
  let some (_, _, accepts) := (← n.state.get).listeners.find? (·.2.1 == addr)
    | return none
  -- `Async` unfolds to a `BaseIO` type, so Lean would elaborate this
  -- `BaseIO` step as an `Async` one. The ascription keeps it `BaseIO`,
  -- and the lift applies (see `Conc.TaskSet.joinAll`).
  let port ← (n.state.updateGet fun s => (s.nextPort, { s with nextPort := s.nextPort + 1 }) :
    BaseIO Nat)
  let localAddr ← memoryAddr port
  let toListener ← Pipe.new simPipeChunks
  let toDialer ← Pipe.new simPipeChunks
  -- The ascriptions keep the steps `BaseIO`, as above.
  let dialerEnd ← (endpoint toDialer toListener localAddr addr n.splitWrites : BaseIO Connection)
  let listenerEnd ← (endpoint toListener toDialer addr localAddr n.splitWrites : BaseIO Connection)
  -- Park: an accept frees a slot, and the close of the listener wakes
  -- the send with `.error .closed`.
  match ← accepts.send listenerEnd with
  | .ok () => return some dialerEnd
  | .error _ =>
    dialerEnd.closeQuietly
    return none

/-- Listen on `addr`. An address in use throws, as a TCP bind does. -/
def listen (n : Net) (addr : Multiaddr) : Async Listener := do
  let accepts : Chan Connection ← Chan.new simBacklog
  -- The ascription keeps the step `BaseIO`, as in `dial`.
  let id ← (n.state.updateGet fun s =>
    if s.listeners.any (·.2.1 == addr) then (none, s)
    else (some s.nextListener,
      { s with listeners := (s.nextListener, addr, accepts) :: s.listeners,
               nextListener := s.nextListener + 1 }) : BaseIO (Option Nat))
  let some id := id
    | throw <| IO.Error.alreadyExists none 0 s!"sim: {addr.describe} is in use"
  let shut : BaseIO Unit := do
    -- The registration number removes this listener only, also after a
    -- new listener took the address.
    n.state.update fun s => { s with listeners := s.listeners.filter (·.1 != id) }
    accepts.close
    -- A send after the close fails, so the drain sees every queued
    -- connection, and their dialers read EOF.
    for c in ← accepts.drain do c.closeQuietly
  return {
    addr
    -- Park: a dial wakes it, and so does the close.
    accept := accepts.recv
    close := do shut
    -- The sim runs no task of its own.
    join := pure () }

/-- The `Transport` value of the network. The sim takes the place of the
whole network of a test, so it handles every address: a suite listens
on `/memory/…` and `/ip4/…/tcp/…` addresses alike. -/
def transport (n : Net) : Transport where
  handles _ := true
  dial := n.dial
  listen := n.listen

end Net

/-- The echo side of a connection: write back each chunk, and close at
EOF. A peer can close before the echo of its last chunk. The write then
fails, and the failed write tore the connection down already
(`Connection.write`). That is the end of the exchange, so `echo` ends
with it and throws nothing. A fault of the read still throws, and the
owner sees it at the join. -/
def echo (c : Connection) : Async Unit := do
  repeat
    match ← c.read with
    | some chunk =>
      let wrote ← try c.write chunk; pure true catch _ => pure false
      if !wrote then break
    | none => break
  c.close

/-- Serve echo on the listener until it closes. Each accepted connection
runs `echo` as a task of `owner`, and the caller joins `owner` after it
closes the listener (§4.1, rule 2). -/
def serveEcho (l : Listener) (owner : TaskSet) : Async Unit := do
  repeat
    -- Park: a dial wakes it, and so does the close of the listener.
    let some c ← l.accept | break
    owner.spawn (echo c)

end Streams.Sim
