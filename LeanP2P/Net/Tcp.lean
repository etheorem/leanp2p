import LeanP2P.Net.Transport
import LeanP2P.Conc
import Std.Internal.UV.TCP
/-!
# TCP transport (VECTOR_TEST_PLAN.md, phase 4 step 23)

Real loopback/network TCP over the toolchain's libuv bindings
(`Std.Internal.UV.TCP`, present in v4.34). Byte-stream semantics hold by
construction: a `read` returns whatever prefix arrived (no message
boundaries), `write`s may split — the framing layers reassemble.

Close semantics, given the runtime's cancellation rules:

- a pending `recv`/`accept` promise is *dropped* (never resolved) by
  `cancelRecv`/`cancelAccept`, so we never cancel; instead `close`
  resolves the pending promise itself (a second resolve is a no-op in the
  task manager), which deterministically unblocks the parked task;
- `close` also sends FIN (`shutdown`), so the peer's readers see EOF and
  its tasks terminate — every task stays joinable.

Listener: `listen` returns a `Listener` whose `accept` reads a channel fed
by one accept-loop task; `close` closes the channel and wakes the accept
loop through its parked promise, then joins it.
-/

namespace LeanP2P.Tcp

open Std.Net
open Std.Internal.UV

/-- Wait for an I/O promise; a promise dropped without ever resolving
(cancel paths we do not use) surfaces as an error. -/
def await (pr : IO.Promise (Except IO.Error α)) : IO (Except IO.Error α) := do
  match ← IO.wait pr.result? with
  | some res => pure res
  | none => pure (.error (IO.userError "promise dropped without resolving"))

/-! ## Multiaddr <-> socket address -/

/-- `/ip4/a.b.c.d/tcp/p` or `/ip6/.../tcp/p` to a socket address. A
trailing `/p2p/<id>` suffix (bootstrap-style addresses) is tolerated and
ignored; `Host.dial` uses it as the expected peer id. -/
def sockAddr? (a : Multiaddr) : Option SocketAddress :=
  -- a trailing /p2p/<id> (bootstrap-style) is tolerated and ignored
  let comps := match a.components.getLast? with
    | some (.p2p _ _) => a.components.dropLast
    | _ => a.components
  match comps with
  | [AddrComponent.ip4 a b c d, AddrComponent.tcp p] =>
      if a < 256 ∧ b < 256 ∧ c < 256 ∧ d < 256 ∧ p < 65536 then
        some (.v4 { addr := { octets := #v[a.toUInt8, b.toUInt8, c.toUInt8, d.toUInt8] }
                    port := p.toUInt16 })
      else none
  | [AddrComponent.ip6 groups, AddrComponent.tcp p] =>
      match groups with
      | [a, b, c, d, e, f, g, h] =>
        if groups.all (· < 65536) ∧ p < 65536 then
          some (.v6 { addr := { segments := #v[a.toUInt16, b.toUInt16, c.toUInt16,
                                              d.toUInt16, e.toUInt16, f.toUInt16,
                                              g.toUInt16, h.toUInt16] }
                      port := p.toUInt16 })
        else none
      | _ => none
  | _ => none

/-- A socket address back to its Multiaddr form. -/
def addrOfSock (sa : SocketAddress) : Multiaddr :=
  match sa with
  | .v4 s =>
      let o := s.addr.octets
      { components := [AddrComponent.ip4 o[0]!.toNat o[1]!.toNat o[2]!.toNat o[3]!.toNat,
                       AddrComponent.tcp s.port.toNat] }
  | .v6 s =>
      let segs := s.addr.segments.toArray.toList.map (·.toNat)
      { components := [AddrComponent.ip6 segs, AddrComponent.tcp s.port.toNat] }

def emptyAddr : Multiaddr :=
  { components := [] }

/-- Best-effort local address of a socket (empty on lookup failure). -/
def localAddrOf (sock : TCP.Socket) : IO Multiaddr := do
  match ← EIO.toIO' (sock.getSockName : EIO IO.Error SocketAddress) with
  | .ok sa => pure (addrOfSock sa)
  | .error _ => pure emptyAddr

/-! ## Connections -/

/-- The parked-read registry so `close` can wake the reader. -/
structure TcpState where
  closed : IO.Ref Bool
  pendingRead : IO.Ref (Option (IO.Promise (Except IO.Error (Option ByteArray))))

/-- `read` parks on one `recv` promise at a time; `close` resolves it.
An empty chunk (never seen in practice) just re-arms the receive. -/
partial def readLoop (st : TcpState) (sock : TCP.Socket) :
    IO (Option ByteArray) := do
  if ← st.closed.get then return none
  -- recv? itself can throw (dead handle, parallel recv); both surface as EOF
  let pr ← try sock.recv? 65536 catch _ => return none
  st.pendingRead.set pr
  if ← st.closed.get then
    -- close already ran before we published the promise: wake ourselves
    pr.resolve (.ok none)
  let res ← await pr
  st.pendingRead.set none
  match res with
  | .error _ => pure none
  | .ok none => pure none
  | .ok (some b) =>
      if b.isEmpty then readLoop st sock else pure (some b)

/-- Wake the parked reader with EOF and FIN the peer: how a failed write
surfaces as connection teardown, so the mux/session layers (and the
application's stream reads) observe the failure instead of hanging. -/
def teardownAfterWriteError (st : TcpState) (sock : TCP.Socket) : IO Unit := do
  unless ← st.closed.get do
    st.closed.set true
    match ← st.pendingRead.get with
    | some pr => pr.resolve (.ok none)  -- wake the parked reader (EOF)
    | none => pure ()
    try
      let pr ← sock.shutdown
      let _ ← await pr
    catch _ => pure ()

/-- Wrap a connected socket into a `Connection`. -/
def connOfSocket (sock : TCP.Socket) (localA remote : Multiaddr) :
    IO Connection := do
  let st : TcpState :=
    { closed := ← IO.mkRef false
      pendingRead := ← IO.mkRef none }
  let read := readLoop st sock
  let write := fun (b : ByteArray) => do
    unless b.isEmpty do
      if ← st.closed.get then pure ()
      else do
        -- send can throw outright (dead handle); a failed send tears the
        -- connection down (read EOF + FIN) instead of vanishing (phase 5)
        let pr? ← try some <$> sock.send #[b] catch _ => pure none
        let ok ← match pr? with
          | none => pure false
          | some pr => do
            match ← await pr with
            | .ok _ => pure true
            | .error _ => pure false
        unless ok do
          teardownAfterWriteError st sock
  let close := do
    unless ← st.closed.get do
      st.closed.set true
      match ← st.pendingRead.get with
      | some pr => pr.resolve (.ok none)  -- wake the parked reader (EOF)
      | none => pure ()
      -- FIN: the peer's readers see EOF; its close FINs us back
      try
        let pr ← sock.shutdown
        let _ ← await pr
      catch _ => pure ()   -- e.g. already shut down / reset by peer
  return { read := read, write := write, close := close
           localAddr := localA, remoteAddr := remote }

/-! ## Dial -/

def dial (a : Multiaddr) : IO (Option Connection) := do
  let some sa := sockAddr? a | return none
  let sock ← TCP.Socket.new
  try sock.noDelay catch _ => pure ()
  match ← await (← sock.connect sa) with
  | .error _ => return none   -- socket becomes garbage; finalizer closes it
  | .ok _ =>
      let localA ← localAddrOf sock
      some <$> connOfSocket sock localA a

/-! ## Listen -/

structure TcpListener where
  sock : TCP.Socket
  closed : IO.Ref Bool
  /-- the currently parked accept promise, so `close` can wake us -/
  pendingAccept : IO.Ref (Option (IO.Promise (Except IO.Error TCP.Socket)))
  queue : Chan (Option Connection)
  addr : Multiaddr

/-- Accept loop: park on `accept`, publish the promise so `close` can wake
us, then hand the connection to the queue. Exits when the listener
closes or the socket dies. -/
partial def TcpListener.loop (l : TcpListener) : IO Unit := do
  if ← l.closed.get then return ()
  let pr ←
    try
      pure (← l.sock.accept)
    catch _ =>
      let _ ← l.queue.send none
      return ()
  l.pendingAccept.set pr
  if ← l.closed.get then
    -- close ran before we published: nobody will resolve it for us
    pr.resolve (.error (IO.userError "listener closed"))
    l.pendingAccept.set none
    return ()
  match ← await pr with
  | .error _ =>
    l.pendingAccept.set none
    let _ ← l.queue.send none
    return ()
  | .ok client =>
    l.pendingAccept.set none
    if ← l.closed.get then
      -- accept raced with close: drop the connection and stop
      try
        let prS ← client.shutdown
        let _ ← await prS
      catch _ => pure ()
      return ()
    try client.noDelay catch _ => pure ()
    let localA ← localAddrOf client
    let remote ←
      match ← EIO.toIO' (client.getPeerName : EIO IO.Error SocketAddress) with
      | .ok sa => pure (addrOfSock sa)
      | .error _ => pure l.addr
    let conn ← connOfSocket client localA remote
    if ← l.queue.send (some conn) then
      TcpListener.loop l
    else
      return ()   -- queue closed

def listen (a : Multiaddr) : IO (Option Listener) := do
  let some sa := sockAddr? a | return none
  let sock ← TCP.Socket.new
  try sock.bind sa catch _ => return none
  try sock.listen 128 catch _ => return none
  -- resolve port 0 to the real bound port
  let bound ←
    match ← EIO.toIO' (sock.getSockName : EIO IO.Error SocketAddress) with
    | .ok l => pure (addrOfSock l)
    | .error _ => pure a
  let l : TcpListener :=
    { sock := sock
      closed := ← IO.mkRef false
      pendingAccept := ← IO.mkRef none
      queue := ← Chan.new
      addr := bound }
  let t ← IO.asTask (l.loop)
  return (some { addr := bound
                 accept := do
                   match ← l.queue.recv with
                   | some c => pure c  -- `none` in the channel = EOF marker
                   | none => pure none -- channel closed
                 close := do
                   l.closed.set true
                   match ← l.pendingAccept.get with
                   | some pr =>
                     pr.resolve (.error (IO.userError "listener closed"))
                     l.pendingAccept.set none
                   | none => pure ()
                   l.queue.close
                   let _ ← IO.wait t })

/-- The TCP transport. -/
def transport : Transport where
  name := "tcp"
  dial := dial
  listen := listen

end LeanP2P.Tcp
