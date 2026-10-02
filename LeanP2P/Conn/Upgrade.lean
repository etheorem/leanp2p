import LeanP2P.Net.Transport
import LeanP2P.Conn.Security
import LeanP2P.Conn.Mux
import LeanP2P.Conn.Yamux
import LeanP2P.Conn.Mplex
import LeanP2P.Protocol.Multiselect
import LeanP2P.Crypto.PeerId
import LeanP2P.Conc
import Std.Sync.Mutex
/-!
# Upgrader (VECTOR_TEST_PLAN.md, phase 4 step 24)

Upgrades a raw connection into a muxed, peer-identified session, exactly
as libp2p's upgrader does, in two multistream-select steps:

1. **security**: the dialer proposes `/noise`, `/tls/1.0.0`, ... one at a
   time (the listener answers `na` until it knows a protocol); the chosen
   `SecurityProtocol.handshake` runs and authenticates the remote peer.
2. **muxer**: over the encrypted connection, the same negotiation picks
   `/yamux/1.0.0` or `/mplex/6.7.0` (go-libp2p takes this from the Noise
   extensions; negotiating on the wire keeps the spike's security
   protocols interchangeable).

`MuxHandle` is the uniform session view the host works with, whatever
muxer was negotiated. `upgradeOutbound` / `upgradeInbound` return a
`Session` carrying the verified remote `PeerId`.
-/

namespace LeanP2P

/-- Uniform view of a negotiated muxer session. `openStream` takes the
protocol name (mplex carries it in NewStream; the others ignore it);
`isDead` reports whether the session has shut down (the host uses it to
retire dead sessions so a peer can reconnect). -/
structure MuxHandle where
  /-- the negotiated muxer's protocol id -/
  name : String
  openStream : String → IO (Option Stream)
  acceptStream : IO (Option Stream)
  shutdown : IO Unit
  isDead : IO Bool
  /-- background tasks (frame pumps) owned by this session; the host
  joins them on close -/
  tasks : TaskSet

/-- A muxer choice for negotiation: name + role entry points. -/
structure MuxChoice where
  name : String
  client : Connection → IO (Option MuxHandle)
  server : Connection → IO (Option MuxHandle)

/-- A live, upgraded connection to an identified peer. `inbound` records
who dialed and `born` is the upgrade time (mono ms): together they let
the host resolve *simultaneous* dials deterministically without touching
long-lived connections that merely got a second, later connection. -/
structure Session where
  remotePeer : PeerId
  remoteAddr : Multiaddr
  mux : MuxHandle
  inbound : Bool := false
  born : Nat := 0
  /-- host-assigned unique id (weak identity for the dedup bookkeeping;
  0 until the host stamps it) -/
  sid : Nat := 0

/-! ## Muxer selection from the security handshake (go semantics)

go-libp2p's upgrader (vendor p2p/net/upgrader `setupMuxer`) uses the muxer
selected inside the security handshake when there was one and only falls
back to multistream-select otherwise. The selection rule is the noise
transport's `MatchMuxers` (vendor p2p/security/noise `transport.go`):
the **initiator** picks the first muxer of *its own* list that the peer
also advertised; the **responder** walks the *initiator's* advertised
list against its own - both converge on the initiator's preference.
An empty intersection selects nothing (multistream fallback). -/

def Upgrade.matchMuxers (choices : List MuxChoice)
    (localOrder remoteOrder : List String) : Option MuxChoice :=
  (localOrder.filter remoteOrder.contains).find? (fun n => choices.any (·.name == n))
    >>= (fun n => choices.find? (·.name == n))

/-! ## The `framed/1.0.0` muxer choice -/

def MuxSession.toHandle (m : MuxSession) : MuxHandle where
  name := FramedMux.name
  openStream := fun _ => some <$> m.openStream
  acceptStream := m.acceptStream
  shutdown := m.shutdown
  isDead := m.dead.get
  tasks := m.tasks

def FramedChoice : MuxChoice where
  name := FramedMux.name
  client c := do return (← MuxSession.make c 1).toHandle
  server c := do return (← MuxSession.make c 0).toHandle

/-! ## The yamux and mplex choices -/

/-- The yamux and mplex choices: the frame pump and the control-frame
writer run as tracked background tasks owned by the session. -/

def YamuxChoice : MuxChoice where
  name := Yamux.protocol
  client c := do
    let s ← Yamux.YamuxSession.make c true
    let tasks ← TaskSet.new
    tasks.spawn s.pump
    tasks.spawn s.controlLoop
    return some { name := Yamux.protocol
                  openStream := fun _ => s.openStream
                  acceptStream := s.acceptStream
                  shutdown := s.shutdown
                  isDead := s.dead.get
                  tasks := tasks }
  server c := do
    let s ← Yamux.YamuxSession.make c false
    let tasks ← TaskSet.new
    tasks.spawn s.pump
    tasks.spawn s.controlLoop
    return some { name := Yamux.protocol
                  openStream := fun _ => s.openStream
                  acceptStream := s.acceptStream
                  shutdown := s.shutdown
                  isDead := s.dead.get
                  tasks := tasks }

def MplexChoice : MuxChoice where
  name := Mplex.protocol
  client c := do
    let s ← Mplex.MplexSession.make c true
    let tasks ← TaskSet.new
    tasks.spawn s.pump
    return some { name := Mplex.protocol
                  openStream := s.openStream
                  acceptStream := s.acceptStream
                  shutdown := s.shutdown
                  isDead := s.dead.get
                  tasks := tasks }
  server c := do
    let s ← Mplex.MplexSession.make c false
    let tasks ← TaskSet.new
    tasks.spawn s.pump
    return some { name := Mplex.protocol
                  openStream := s.openStream
                  acceptStream := s.acceptStream
                  shutdown := s.shutdown
                  isDead := s.dead.get
                  tasks := tasks }

/-! ## Negotiation -/

/-- Dialer side: propose each security protocol in order (the listener
answers `na` until one matches), then run that handshake. -/
partial def Upgrade.securityInitiator (secs : List SecurityProtocol)
    (c : Connection) : IO (Option (SecureConn × SecurityProtocol)) := do
  let r ← BufReader.ofConn c
  let rec go : List SecurityProtocol → IO (Option (SecureConn × SecurityProtocol))
    | [] => pure none
    | s :: rest => do
      match ← Multiselect.selectInitiator r c s.name with
      | none => go rest
      | some _ =>
        match ← s.handshake .initiator c with
        | none => pure none   -- handshake failure is fatal: stop
        | some sc => pure (some (sc, s))
  go secs

/-- Listener side: answer proposals until a known security protocol
arrives, then run that handshake as responder. -/
def Upgrade.securityResponder (secs : List SecurityProtocol)
    (c : Connection) : IO (Option (SecureConn × SecurityProtocol)) := do
  let r ← BufReader.ofConn c
  match ← Multiselect.selectResponder r c (secs.map (·.name)) with
  | none => pure none
  | some name =>
    match secs.find? (·.name == name) with
    | none => pure none
    | some sec => do
      let sc? ← sec.handshake .responder c
      return (sc?.map fun sc => (sc, sec))

/-- Dialer side: start the muxer chosen in the security handshake, or
multistream-negotiate one when no muxer was agreed. -/
partial def Upgrade.muxInitiator (muxers : List MuxChoice)
    (agreed : Option MuxChoice) (c : Connection) :
    IO (Option (MuxChoice × MuxHandle)) := do
  match agreed with
  | some m => do
    match ← m.client c with
    | none => pure none
    | some h => pure (some (m, h))
  | none =>
    let r ← BufReader.ofConn c
    let rec go : List MuxChoice → IO (Option (MuxChoice × MuxHandle))
      | [] => pure none
      | m :: rest => do
        match ← Multiselect.selectInitiator r c m.name with
        | none => go rest
        | some _ =>
          match ← m.client c with
          | none => pure none
          | some h => pure (some (m, h))
    go muxers

/-- Listener side: start the muxer chosen in the security handshake, or
multistream-negotiate one when no muxer was agreed. -/
def Upgrade.muxResponder (muxers : List MuxChoice)
    (agreed : Option MuxChoice) (c : Connection) :
    IO (Option (MuxChoice × MuxHandle)) := do
  match agreed with
  | some m => do
    match ← m.server c with
    | none => pure none
    | some h => pure (some (m, h))
  | none => do
    let r ← BufReader.ofConn c
    match ← Multiselect.selectResponder r c (muxers.map (·.name)) with
    | none => pure none
    | some name =>
      match muxers.find? (·.name == name) with
      | none => pure none
      | some m => do
        let h? ← m.server c
        return (h?.map fun h => (m, h))

/-- Full outbound upgrade: dial `addr`, negotiate security, verify the
remote identity (`expect`, when given), then start the muxer selected in
the handshake (falling back to multistream-select). -/
def Upgrade.upgradeOutbound (secs : List SecurityProtocol)
    (muxers : List MuxChoice) (transport : Transport) (addr : Multiaddr)
    (expect : Option PeerId) : IO (Option Session) := do
  let some raw ← transport.dial addr | return none
  match ← Upgrade.securityInitiator secs raw with
  | none => raw.close; return none
  | some (sc, _) => do
    match expect with
    | some pid =>
      if sc.remotePeer != pid then
        -- the handshake authenticated a different peer than we dialed
        sc.toConnection.close
        return none
    | none => pure ()
    -- go upgrader semantics: the initiator picks by its own preference
    let agreed := Upgrade.matchMuxers muxers (muxers.map (·.name)) sc.remoteMuxers
    match ← Upgrade.muxInitiator muxers agreed sc.toConnection with
    | none => sc.toConnection.close; return none
    | some (_, h) =>
      return (some { remotePeer := sc.remotePeer
                     remoteAddr := sc.toConnection.remoteAddr
                     mux := h
                     inbound := false
                     born := ← IO.monoMsNow })

/-- Full inbound upgrade: answer the security negotiation, handshake, then
start the muxer selected by the initiator in the handshake (falling back
to multistream-select). -/
def Upgrade.upgradeInbound (secs : List SecurityProtocol)
    (muxers : List MuxChoice) (c : Connection) : IO (Option Session) := do
  match ← Upgrade.securityResponder secs c with
  | none => pure none
  | some (sc, _) => do
    -- responder rule: follow the initiator's (remote) preference order
    let agreed := Upgrade.matchMuxers muxers sc.remoteMuxers (muxers.map (·.name))
    match ← Upgrade.muxResponder muxers agreed sc.toConnection with
    | none => sc.toConnection.close; pure none
    | some (_, h) =>
      pure (some { remotePeer := sc.remotePeer
                   remoteAddr := sc.toConnection.remoteAddr
                   mux := h
                   inbound := true
                   born := ← IO.monoMsNow })

end LeanP2P
