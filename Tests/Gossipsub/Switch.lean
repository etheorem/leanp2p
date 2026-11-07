import Libp2p.Protocols.Gossipsub.HostSeam

set_option autoImplicit false

namespace Tests.Gossipsub

open Libp2p.Identity Libp2p.Core Libp2p.Protocols.Gossipsub

/-! ## The in-memory switch

The switch stands in for the session table of the host and its serve
task. Two peers meet over a pair of pipes, with no transport. -/

/-- One peer of the switch. -/
private structure Switch.Entry where
  /-- The peer. -/
  peer : PeerId
  /-- The handlers the peer registered, the oldest first. -/
  handlers : List Libp2p.Core.StreamHandler
  /-- The owner of the handler tasks of the inbound streams of the peer. -/
  tasks : Conc.TaskSet

/-- The state of a switch. -/
private structure Switch.State where
  /-- The peers. -/
  entries : List Switch.Entry
  /-- Every pipe the switch opened. The list lives as long as the switch,
  which a test double allows. -/
  pipes : List Conc.Pipe
  /-- True after `Switch.close`. -/
  closed : Bool

/-- The in-memory double of the session table: the peers, their handlers,
and the pipes of their streams. -/
structure Switch where
  private state : Conc.OnceRef Switch.State

namespace Switch

/-- A switch with no peers. -/
def new : BaseIO Switch :=
  return ⟨← Conc.OnceRef.new { entries := [], pipes := [], closed := false }⟩

/-- A stream over a pair of pipes. `read` reads `incoming`, and `write`
writes `outgoing`. `close` closes `outgoing`, the half-close. `reset`
closes both, so the peer of a reset reads the end of the stream and its
writes fail. -/
private def streamOf (incoming outgoing : Conc.Pipe) : Streams.Stream where
  read := do
    let chunk ← incoming.read
    return .ok chunk
  write bytes := do
    match ← outgoing.write bytes with
    | .ok () => return .ok ()
    | .error _ => return .error .closed
  close := (outgoing.close : BaseIO Unit)
  reset := do
    (incoming.close : BaseIO Unit)
    (outgoing.close : BaseIO Unit)

/-- The first protocol of the list that the handlers serve, with its
handler. -/
private def choose (handlers : List Libp2p.Core.StreamHandler) :
    List Libp2p.Core.ProtocolId → Option (Libp2p.Core.ProtocolId × Libp2p.Core.StreamHandler)
  | [] => none
  | p :: ps =>
    match handlers.find? (fun h => decide (h.id = p)) with
    | some h => some (p, h)
    | none => choose handlers ps

/-- Run one handler on an inbound stream. A handler error fails the task,
so the `joinAll` of the owner reports it. -/
private def serve (handler : Libp2p.Core.StreamHandler) (peer : PeerId)
    (stream : Streams.Stream) : Conc.Async Unit := do
  match ← (handler.handle { remotePeer := peer, remoteAddr := Multiformats.Multiaddr.empty } stream).run with
  | .ok () => return ()
  | .error e => throw <| IO.userError s!"handler {handler.id.toString}: {repr e}"

/-- Open a stream from `me` to `peer`: pick the protocol, make the pipes,
spawn the handler on the task set of `peer`, and answer the initiator
stream. The call never parks. Eight chunks is far more than one RPC frame
needs, and the bound stays explicit. -/
private def open_ (sw : Switch) (me peer : PeerId) (protocols : List Libp2p.Core.ProtocolId) :
    BaseIO (Except Libp2p.Core.Error (Libp2p.Core.ProtocolId × Streams.Stream)) := do
  let st ← sw.state.get
  let some entry := st.entries.find? (fun e => decide (e.peer = peer))
    | return .error (.protocol s!"no peer {peer}")
  let some (id, handler) := choose entry.handlers protocols
    | return .error (.protocol s!"peer {peer} serves none of the protocols")
  let toPeer ← Conc.Pipe.new 8
  let fromPeer ← Conc.Pipe.new 8
  -- One atomic step checks the flag and records the pipes, so `close`
  -- sees every pipe of a stream that opens before it.
  let opened ← sw.state.updateGet fun s =>
    if s.closed then (false, s)
    else (true, { s with pipes := toPeer :: fromPeer :: s.pipes })
  if !opened then return .error (.closed "the switch closed")
  entry.tasks.spawn (serve handler me (streamOf toPeer fromPeer))
  return .ok (id, streamOf fromPeer toPeer)

/-- The seam of the peer `me`, and the task set that owns the handler
tasks of its inbound streams. Each peer starts with an empty handler
table, and a handler registered through one seam serves only that peer. -/
def host (sw : Switch) (me : PeerId) : BaseIO (HostSeam × Conc.TaskSet) := do
  let tasks ← Conc.TaskSet.new
  sw.state.update fun s =>
    { s with
      entries := { peer := me, handlers := [], tasks } ::
        s.entries.filter (fun e => decide (e.peer ≠ me)) }
  let seam : HostSeam :=
    { newStream := fun peer protocols => (sw.open_ me peer protocols : BaseIO _)
      setHandler := fun handler =>
        sw.state.update fun s =>
          { s with
            entries := s.entries.map fun e =>
              if e.peer = me then { e with handlers := e.handlers ++ [handler] } else e } }
  return (seam, tasks)

/-- End every stream the switch opened, then join the handler tasks
(ARCHITECTURE §4.1, rule 2). A close wakes every parked read and write.
A failed handler task does not stop the joins of the other peers. The call
throws the first error after the last join. A second call does nothing. -/
def close (sw : Switch) : Conc.Async Unit := do
  let st ← (sw.state.updateGet (fun s => (s, { s with closed := true, pipes := [] })) :
    BaseIO Switch.State)
  for p in st.pipes do
    (p.close : BaseIO Unit)
  let mut failure : Option IO.Error := none
  for e in st.entries do
    try
      e.tasks.joinAll
    catch err =>
      failure := failure <|> some err
  if let some err := failure then throw err

end Switch

end Tests.Gossipsub
