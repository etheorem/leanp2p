import Std.Data.HashMap
import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Host.Error
import Libp2p.Host.StreamSelect
import Libp2p.Host.Upgrade
import Libp2p.Host.Registry
import Libp2p.Host.Dedup
import Libp2p.Host.Peerstore
import Libp2p.Host.Policy
import Libp2p.Host.Gate

/-!
# The swarm

The host composes the stack into a node (ARCHITECTURE §4.9). This
module holds its configuration, its state, and its paths:

* the dial path: `dial` and `dialPeer` pick a transport by the address
  (`Transport.handles`), dial, and run the upgrade;
* the listen path: `startListening` binds a listener, and its accept
  loop runs each accepted connection through the upgrade;
* the secured paths: an address that a `SecuredTransport` handles goes
  to it first. Its sessions arrive secured and muxed, so they skip the
  upgrade. They still meet its checkpoint, the dedup, and the serve
  task of any session;
* the session paths: a committed session runs one serve task, which
  accepts the peer's streams, negotiates each one against the handler
  table, and hands it to its handler; `newStream` opens and negotiates
  an outbound stream.

`Libp2p.Host.Shutdown` holds `close`.

## The upgrade and its checkpoints

The policy hooks answer at the checkpoints of the core pair, in the
order the go-libp2p swarm and upgrader call them (the package
ARCHITECTURE, "Refinements fixed at implementation (unit 1b)"):
`allowDial` before a dial, `allowInbound` after an accept, the
resource manager's `openConnection` before the upgrade, and
`allowSecured` and `ConnectionScope.setPeer` inside the upgrade, after
the handshake and before the muxer stage (`Libp2p.Host.upgrade`). A
refusal is `Error.gated` with the checkpoint.

## Ownership

Every task has an owner that joins it (PRINCIPLES 3.2):

* the accept loop of a listener, and the upgrade of each accepted
  connection, run in the gate `hostTasks`;
* the serve task of a committed session runs in the gate
  `sessionTasks`;
* the task of one inbound stream runs in a `TaskSet` that its
  session's serve task owns, and joins when the session ends.

A failure of a task that no caller awaits goes to the owner of the
host through `Config.onFailure`, with the peer and the protocol when
they are known (§3.5: an owner never learns of a failure by EOF).

## The race with the shutdown

`close` sets the closing flag first (§5.5). A path that registers
something the shutdown must reach (a listener, a pending connection, a
session) registers it, then reads the flag. When the flag is set, the
path closes what it registered itself. Otherwise the flag came later,
so the shutdown sees the registration and closes it. The gates refuse
a task that starts after the shutdown joined their group, and the
refused caller closes and joins the work itself (`Gate.spawn`).
-/

set_option autoImplicit false

namespace Libp2p.Host

open Conc Streams Multiformats Libp2p.Identity Libp2p.Core

/-- A failure of a task that no caller awaits: an inbound upgrade, a
session that ended badly, an inbound stream. -/
structure Failure where
  /-- The peer, once the handshake proved it. -/
  peer : Option PeerId
  /-- The protocol of the stream, once its negotiation selected one. -/
  protocol : Option ProtocolId
  /-- What failed. -/
  error : Error

/-- The configuration of a host: the ordered seam lists, the identity,
the handlers, the policy values, the clock, and where the failures of
owned tasks go (ARCHITECTURE §3.1). `cli/` or a consumer assembles it;
no host module names a concrete transport, security protocol, or
muxer. -/
structure Config where
  /-- The host identity. The local peer id derives from it. The
  security values carry their own copy of the key, as their
  configuration needs it. -/
  identity : PrivKey
  /-- The transports. An address picks the first one that handles it. -/
  transports : List Transport
  /-- The secured transports, such as QUIC: their connections arrive
  secured and muxed, so the upgrade has no stage to run on them. An
  address that one of them handles goes to it before the list above
  (the package ARCHITECTURE, "Secured transports"). -/
  securedTransports : List SecuredTransport := []
  /-- The security protocols, in preference order. -/
  security : List SecurityProtocol
  /-- The muxers, in preference order. -/
  muxers : List Muxer
  /-- The handlers the host starts with. -/
  handlers : List StreamHandler := []
  /-- The connection gater. -/
  gater : ConnectionGater := Policy.permissiveGater
  /-- The resource manager. -/
  resources : ResourceManager := Policy.unlimited
  /-- The address ranker of `dialPeer`: QUIC first, as the consensus
  networking spec asks (`Policy.quicFirst`). -/
  ranker : AddressRanker := Policy.quicFirst
  /-- The clock of the upgrade deadline, the session births, and the
  dial delays. -/
  clock : Clock := Clock.system
  /-- Where the failures of owned tasks go. It runs on the failing
  task, so it answers at once. -/
  onFailure : Failure → BaseIO Unit := fun _ => pure ()

/-- A session the host serves: the upgraded connection, the peer's
transport address, and the resource scope it holds. -/
structure Served where
  /-- The upgrade's answer: the muxer session, the proved peer, and
  the join of the session and the secure connection. -/
  upgraded : Upgraded
  /-- The connection's remote address; every served stream's
  `StreamContext` carries it. -/
  remoteAddr : Multiaddr
  /-- The connection's resource scope; the serve task releases it when
  the session ends. -/
  scope : ConnectionScope

/-- A running host. Every cell changes through `OnceRef.update` or
`OnceRef.updateGet` (contract 1). -/
structure Host where
  /-- The configuration. -/
  config : Config
  /-- Our peer id, derived from `config.identity`. -/
  localPeer : PeerId
  /-- The session table (§3.8). -/
  sessions : OnceRef (SessionTable Served)
  /-- The handler table (§3.10). -/
  handlers : OnceRef Handlers
  /-- The peerstore (§3.8). -/
  peerstore : OnceRef Peerstore
  /-- The next session number, and the next pending key. -/
  counter : OnceRef Nat
  /-- The closing flag (§5.5). -/
  closing : OnceRef Bool
  /-- Closed by `close` first, so a dial delay that waits on it wakes. -/
  shutdown : Chan Unit
  /-- The listeners; `none` once `close` took them. -/
  listeners : OnceRef (Option (List Listener))
  /-- The listeners of the secured transports; `none` once `close`
  took them. -/
  securedListeners : OnceRef (Option (List SecuredListener))
  /-- The connections inside their upgrade, the pending connections of
  §5.5; `none` once `close` took them. -/
  pending : OnceRef (Option (Std.HashMap Nat Connection))
  /-- The serve tasks of the sessions. -/
  sessionTasks : Gate
  /-- The accept loops and the inbound upgrades. -/
  hostTasks : Gate

namespace Host

/-- A host over `config`. `.error` when the identity key derives no
peer id. -/
def new (config : Config) : BaseIO (Except Identity.Error Host) := do
  match config.identity.toPublic.bind PeerId.ofPubKey with
  | .error e => return .error e
  | .ok localPeer =>
    return .ok {
      config, localPeer
      sessions := ← OnceRef.new {}
      handlers := ← OnceRef.new (config.handlers.foldl (fun t h => Handlers.set h t) {})
      peerstore := ← OnceRef.new {}
      counter := ← OnceRef.new 0
      closing := ← OnceRef.new false
      shutdown := ← Chan.new 1
      listeners := ← OnceRef.new (some [])
      securedListeners := ← OnceRef.new (some [])
      pending := ← OnceRef.new (some {})
      sessionTasks := ← Gate.new
      hostTasks := ← Gate.new }

/-! ## Small steps -/

/-- A fresh number, for a session or a pending connection. -/
private def draw (h : Host) : BaseIO Nat :=
  h.counter.updateGet fun n => (n, n + 1)

/-- True once `close` has begun. -/
def isClosing (h : Host) : BaseIO Bool :=
  h.closing.get

/-- Hand a failure to the owner of the host. -/
private def report (h : Host) (peer : Option PeerId) (protocol : Option ProtocolId)
    (error : Error) : BaseIO Unit :=
  h.config.onFailure { peer, protocol, error }

/-- Store `handler` under its id, through the cell's update (contract
1). A served stream negotiated after the call sees it. -/
def setHandler (h : Host) (handler : StreamHandler) : BaseIO Unit :=
  h.handlers.update (Handlers.set handler)

/-- Add addresses of `peer` to the peerstore, each once. -/
def addAddrs (h : Host) (peer : PeerId) (addrs : List Multiaddr) : BaseIO Unit :=
  h.peerstore.update (Peerstore.addAddrs peer addrs)

/-- The addresses of `peer` in the peerstore. -/
def addrsOf (h : Host) (peer : PeerId) : BaseIO (List Multiaddr) := do
  return Peerstore.addrsOf (← h.peerstore.get) peer

/-- True when the host serves a live session with `peer`. -/
def connected (h : Host) (peer : PeerId) : BaseIO Bool := do
  return (SessionTable.live? (← h.sessions.get) peer).isSome

/-- The transport address and the expected peer of a dial address. A
trailing `/p2p/<id>` names the peer and no transport (the addressing
spec, "The p2p multiaddr"), so it comes off before the transport
lookup, as go-libp2p's swarm drops it (the package ARCHITECTURE, unit
1b). The component's value is the peer id's binary form, the multihash
bytes. An address that is only `/p2p/<id>` has no transport part. -/
def splitPeer (a : Multiaddr) : Except Error (Multiaddr × Option PeerId) :=
  match a.components.getLast? with
  | some c =>
    if c.proto = .«p2p» then
      -- The multiaddr check already accepted the value as a peer id
      -- multihash, so both lookups succeed on every valid address. The
      -- value is in the `List Nat` byte model, and `PeerId.ofBytes?`
      -- reads a `ByteArray`.
      match (PeerId.ofBytes? (Bytes.ofNatList c.value)).toOption,
        (a.decapsulateCode (Protocol.toCode .«p2p»)).toOption with
      -- An empty rest is a valid address (root §4.4: it prints as `/`),
      -- and it names no transport.
      | some p, some t => if t.components.isEmpty then .error (.noTransport a) else .ok (t, some p)
      | _, _ => .error (.noTransport a)
    else .ok (a, none)
  | none => .ok (a, none)

/-- The checkpoint the upgrade runs after the handshake (the module
doc, "The upgrade and its checkpoints"), at the two addresses of the
connection. A secured transport's session meets the same checkpoint
(`admitSecured`). -/
private def admitAt (h : Host) (role : Role) (scope : ConnectionScope)
    (localAddr remoteAddr : Multiaddr) (peer : PeerId) : BaseIO (Option Checkpoint) := do
  if !(← h.config.gater.allowSecured role peer localAddr remoteAddr) then
    return some .secured
  if !(← scope.setPeer peer) then return some .resources
  return none

/-- The checkpoint of `admitAt`, at the addresses of a connection. -/
private def admit (h : Host) (role : Role) (scope : ConnectionScope) (conn : Connection)
    (peer : PeerId) : BaseIO (Option Checkpoint) :=
  h.admitAt role scope conn.localAddr conn.remoteAddr peer

/-! ## The upgrade -/

/-- Run the upgrade of `conn` as a pending connection: registered for
the shutdown (§5.5), under the deadline of the upgrade, with the
checkpoint. Every failure releases `scope`. On a failure, the upgrade
already closed the connection. -/
private def upgradeConn (h : Host) (role : Role) (conn : Connection) (expected : Option PeerId)
    (scope : ConnectionScope) : Async (Except Error Upgraded) := do
  let key ← (h.draw : BaseIO Nat)
  let registered ← (h.pending.updateGet fun
    | some m => (true, some (m.insert key conn))
    | none => (false, none) : BaseIO Bool)
  -- The registration, then the flag (the module doc, "The race with
  -- the shutdown").
  if !registered || (← (h.isClosing : BaseIO Bool)) then
    conn.closeQuietly
  let unregister : BaseIO Unit := h.pending.update (·.map (·.erase key))
  let r ← try
      (upgrade h.config.clock role conn expected (h.admit role scope conn)
        h.config.security h.config.muxers).run
    catch e =>
      unregister
      scope.release
      throw e
  unregister
  match r with
  | .ok (.upgraded u) => return .ok u
  | .ok (.refused c) =>
    scope.release
    return .error (.gated c)
  | .error e =>
    scope.release
    return .error (if ← (h.isClosing : BaseIO Bool) then .closing else .upgrade e)

/-! ## Serving -/

/-- Serve one inbound stream: admit it, negotiate its protocol against
the handler table, and run the handler. A refused admission, a failed
negotiation, an id with no handler, and a failed handler each reset
the stream, and the session stays (contracts 5 and 6; the package
ARCHITECTURE, public surface). -/
private def serveStream (h : Host) (ctx : StreamContext) (scope : ConnectionScope)
    (s : Stream) : Async Unit := do
  let peer := ctx.remotePeer
  let some share ← (scope.reserveStream : BaseIO (Option Reservation))
    | s.reset
  let ids := Handlers.ids (← (h.handlers.get : BaseIO Handlers))
  match ← (negotiateStream .responder s ids).run with
  | .error e =>
    s.reset
    share.release
    -- The peer ended the stream before it chose a protocol: an orderly
    -- end, not a failure.
    unless e matches .closed _ do
      h.report (some peer) none (.stream e)
  | .ok (id, s) =>
    match (← (h.handlers.get : BaseIO Handlers)).find? id with
    | none =>
      -- The negotiation selected an id from the table's ids, and the
      -- handler left the table since; the stream closes (contract 6).
      s.reset
      share.release
    | some handler =>
      -- The handler owns the stream from here. Its answer reaches the
      -- owner of the host; a fault passes on to the session's join.
      let r ← try (handler.handle ctx s).run
        catch e =>
          s.reset
          share.release
          throw e
      share.release
      if let .error e := r then
        s.reset
        h.report (some peer) (some id) (.stream e)

/-- Serve a committed session until it ends: accept the peer's
streams, and serve each one in a task of this session. At the end, mark
the entry dead (contract 3), join the stream tasks, release the scope,
and join the session. -/
private def serveSession (h : Host) (peer : PeerId) (e : Entry Served) : Async Unit := do
  let u := e.session.upgraded
  let ctx : StreamContext := { remotePeer := peer, remoteAddr := e.session.remoteAddr }
  let streams ← TaskSet.new
  let acceptFault ← try
      repeat
        -- Park: a stream of the peer wakes it, and so does the end of the
        -- session, by the peer or by `MuxSession.close` (contract 4).
        let some s ← u.session.accept | break
        streams.spawn (h.serveStream ctx e.session.scope s)
      pure (none : Option IO.Error)
    catch err => pure (some err)
  h.sessions.update (SessionTable.markDead peer e.id)
  discard u.session.close.toBaseIO
  -- The session has ended, so every stream read ends, and the handlers
  -- that park on their streams wake.
  let streamFault ← try streams.joinAll; pure (none : Option IO.Error)
    catch err => pure (some err)
  e.session.scope.release
  let joinFault ← try
      if let .error ce ← u.join.run then
        h.report (some peer) none (.session ce)
      pure (none : Option IO.Error)
    catch err => pure (some err)
  if let some err := acceptFault <|> streamFault <|> joinFault then throw err

/-- Commit an upgraded session through the dedup rule (contract 2), and
start its serve task. The answer is the peer the host now serves. -/
private def register (h : Host) (role : Role) (u : Upgraded) (remoteAddr : Multiaddr)
    (scope : ConnectionScope) : Async (Except Error PeerId) := do
  let id ← (h.draw : BaseIO Nat)
  let bornMs ← (h.config.clock.nowMs : BaseIO Nat)
  let entry : Entry Served :=
    { id, role, bornMs, live := true, session := { upgraded := u, remoteAddr, scope } }
  let decision ← (h.sessions.updateGet (dedup h.localPeer u.remotePeer entry) :
    BaseIO (Decision Served))
  match decision with
  | .keep _ =>
    -- The standing session serves the peer; the candidate ends here. Its
    -- join answer is dropped: we ended it. A fault still passes on, after
    -- the scope is back.
    discard u.session.close.toBaseIO
    try discard u.join.run
    finally scope.release
    return .ok u.remotePeer
  | .commit displaced =>
    -- A displaced session ends; its own serve task marks it dead and
    -- joins it.
    if let some old := displaced then
      discard old.session.upgraded.session.close.toBaseIO
    let wake : BaseIO Unit := discard u.session.close.toBaseIO
    if !(← h.sessionTasks.spawn (h.serveSession u.remotePeer entry) wake) then
      return .error .closing
    -- The registration, then the flag (the module doc).
    if ← (h.isClosing : BaseIO Bool) then
      wake
      return .error .closing
    return .ok u.remotePeer

/-! ## The secured sessions -/

/-- Admit a session that a secured transport proved: the checkpoint of
the upgrade, at the session's addresses, then the dedup and the serve
task. A refusal closes the session and releases `scope`. -/
private def admitSecured (h : Host) (role : Role) (s : SecuredSession) (scope : ConnectionScope) :
    Async (Except Error PeerId) := do
  if let some c ← (h.admitAt role scope s.localAddr s.remoteAddr s.remotePeer :
      BaseIO (Option Checkpoint)) then
    discard s.session.close.toBaseIO
    discard s.session.join.run
    scope.release
    return .error (.gated c)
  h.register role { session := s.session, remotePeer := s.remotePeer } s.remoteAddr scope

/-- Dial a secured transport. The transport proves the peer, so the
dial has no pending connection to register: its handshake has its own
deadline inside the transport (root §5.4), and the host's shutdown
channel ends it at a close (root §5.5; the package ARCHITECTURE,
"Secured transports"). -/
private def dialSecured (h : Host) (t : SecuredTransport) (addr : Multiaddr)
    (expected : Option PeerId) : Async (Except Error PeerId) := do
  let some scope ← (h.config.resources.openConnection .initiator expected addr :
      BaseIO (Option ConnectionScope))
    | return .error (.gated .resources)
  -- The shutdown channel, which stage 1 of `close` closes, ends a dial
  -- still in its handshake (§5.5).
  let r ← try (t.dial addr expected h.shutdown).run
    catch e =>
      scope.release
      throw e
  match r with
  | .error e =>
    scope.release
    return .error (if ← (h.isClosing : BaseIO Bool) then .closing else .upgrade e)
  | .ok s =>
    let r ← h.admitSecured .initiator s scope
    if let .ok p := r then h.addAddrs p [addr]
    return r

/-! ## The dial path -/

/-- Dial one transport address and upgrade it, or reuse the live
session of `expected`. -/
private def dialAddr (h : Host) (addr : Multiaddr) (expected : Option PeerId) :
    Async (Except Error PeerId) := do
  if ← (h.isClosing : BaseIO Bool) then return .error .closing
  if expected == some h.localPeer then return .error .dialSelf
  if let some p := expected then
    if ← (h.connected p : BaseIO Bool) then return .ok p
  if !(← (h.config.gater.allowDial expected addr : BaseIO Bool)) then
    return .error (.gated .dial)
  if let some t := h.config.securedTransports.find? (·.handles addr) then
    return ← h.dialSecured t addr expected
  let some transport := h.config.transports.find? (·.handles addr)
    | return .error (.noTransport addr)
  let some scope ← (h.config.resources.openConnection .initiator expected addr :
      BaseIO (Option ConnectionScope))
    | return .error (.gated .resources)
  let dialed ← try transport.dial addr
    catch e =>
      scope.release
      throw e
  let some conn := dialed
    | scope.release
      return .error (.unreachable addr)
  match ← h.upgradeConn .initiator conn expected scope with
  | .error e => return .error e
  | .ok u =>
    let r ← h.register .initiator u conn.remoteAddr scope
    if let .ok p := r then h.addAddrs p [addr]
    return r

/-- Dial an address, or reuse a live session (the package
ARCHITECTURE, public surface). The expected peer is `peer`, or, when
the call gives none, the trailing `/p2p/<id>` of the address. The
answer is the peer the handshake proved. -/
def dial (h : Host) (addr : Multiaddr) (peer : Option PeerId := none) :
    Async (Except Error PeerId) := do
  match splitPeer addr with
  | .error e => return .error e
  | .ok (transportAddr, fromAddr) => h.dialAddr transportAddr (peer <|> fromAddr)

/-- Dial `peer` through its peerstore addresses, in the ranker's
schedule, until one dial succeeds. The answer is the failure of the
last address when none does. -/
def dialPeer (h : Host) (peer : PeerId) : Async (Except Error PeerId) := do
  if peer == h.localPeer then return .error .dialSelf
  if ← (h.connected peer : BaseIO Bool) then return .ok peer
  let addrs ← (h.addrsOf peer : BaseIO (List Multiaddr))
  if addrs.isEmpty then return .error (.noAddresses peer)
  let start ← (h.config.clock.nowMs : BaseIO Nat)
  let mut last : Error := .noAddresses peer
  for step in h.config.ranker.rank addrs do
    let now ← (h.config.clock.nowMs : BaseIO Nat)
    if now < start + step.delayMs then
      let timer ← (h.config.clock.after (start + step.delayMs - now) : BaseIO (Park Unit))
      -- Park: the timer wakes it, and so does `close`, which closes
      -- `shutdown` first (PRINCIPLES 3.1).
      select #[timer, Park.recv h.shutdown fun _ => ()]
    match ← h.dialAddr step.addr (some peer) with
    | .ok p => return .ok p
    | .error .closing => return .error .closing
    | .error e => last := e
  return .error last

/-! ## The listen path -/

/-- The admission of an inbound connection before its handshake
(`Policy.admission`): the gater's `allowInbound`, then the resource
manager's scope. A TCP connection meets it at its accept, and a secured
transport's connection when its first packet arrives. -/
private def admitInbound (h : Host) : Admit :=
  Policy.admission h.config.gater h.config.resources

/-- Upgrade one accepted connection. No caller awaits it, so its
failure goes to the owner of the host; a refusal by policy is a
decision, and no failure. -/
private def inbound (h : Host) (conn : Connection) : Async Unit := do
  let some scope ← (h.admitInbound conn.localAddr conn.remoteAddr :
      BaseIO (Option ConnectionScope))
    | conn.closeQuietly
  match ← h.upgradeConn .responder conn none scope with
  | .ok u =>
    if let .error e ← h.register .responder u conn.remoteAddr scope then
      unless e matches .closing do h.report (some u.remotePeer) none e
  | .error (.gated _) | .error .closing => pure ()
  | .error e => h.report none none e

/-- The accept loop of a listener: each accepted connection upgrades
in a task of `hostTasks`. -/
private def acceptLoop (h : Host) (l : Listener) : Async Unit := do
  repeat
    -- Park: a dialed connection wakes it, and so does the listener's
    -- close (contract 4).
    let some conn ← l.accept | break
    discard <| h.hostTasks.spawn (h.inbound conn) conn.closeQuietly

/-- Admit one session of a secured listener, with the scope its
admission opened before the handshake (`admitInbound`). No caller
awaits it, so its failure goes to the owner of the host; a refusal by
policy is a decision, and no failure. -/
private def inboundSecured (h : Host) (s : SecuredSession) (scope : ConnectionScope) :
    Async Unit := do
  match ← h.admitSecured .responder s scope with
  | .ok _ | .error (.gated _) | .error .closing => pure ()
  | .error e => h.report (some s.remotePeer) none e

/-- The accept loop of a secured listener: each session is admitted in
a task of `hostTasks`. A session the task set refuses, at a close,
closes and releases its scope. -/
private def acceptSecuredLoop (h : Host) (l : SecuredListener) : Async Unit := do
  repeat
    -- Park: a proved session wakes it, and so does the listener's close
    -- (contract 4).
    let some (s, scope) ← l.accept | break
    discard <| h.hostTasks.spawn (h.inboundSecured s scope) do
      discard s.session.close.toBaseIO
      scope.release

/-- Adopt a listener that a transport has bound: register it in `cell`,
the host's list of its kind, and spawn its accept loop. `close` takes
the list once (the module doc), so a listener that comes after it is
this call's to close and join. The registration comes before the flag
test: `close` holds the listener in its list, and it joins the listener
after the host tasks. -/
private def adoptListener {L : Type} (h : Host) (cell : OnceRef (Option (List L))) (l : L)
    (addr : Multiaddr) (close : IO Unit) (join : Async Unit) (acceptLoop : Async Unit) :
    Async (Except Error Multiaddr) := do
  let registered ← (cell.updateGet fun
    | some ls => (true, some (l :: ls))
    | none => (false, none) : BaseIO Bool)
  if !registered then
    -- `close` took the listeners already, so this call owns `l`.
    close
    join
    return .error .closing
  if !(← h.hostTasks.spawn acceptLoop (discard close.toBaseIO)) then
    join
    return .error .closing
  if ← (h.isClosing : BaseIO Bool) then
    close
    return .error .closing
  return .ok addr

/-- Listen on an address through the first transport that handles it,
and start its accept loop. A secured transport that handles the address
goes first, and it admits each connection through `admitInbound` before
its handshake. The answer is the address the listener serves, with the
port the system picked for a port of 0. -/
def startListening (h : Host) (addr : Multiaddr) : Async (Except Error Multiaddr) := do
  if ← (h.isClosing : BaseIO Bool) then return .error .closing
  if let some t := h.config.securedTransports.find? (·.handles addr) then
    let l ← t.listen addr h.admitInbound
    return ← h.adoptListener h.securedListeners l l.addr l.close l.join (h.acceptSecuredLoop l)
  let some transport := h.config.transports.find? (·.handles addr)
    | return .error (.noTransport addr)
  let l ← transport.listen addr
  h.adoptListener h.listeners l l.addr l.close l.join (h.acceptLoop l)

/-! ## Outbound streams -/

/-- Open a stream to `peer` and negotiate one of `protocols`, in
preference order. The host dials the peer through the peerstore when no
session is live. The answer is the selected id and the stream, with
the bytes the negotiation over-read at its front (§4.7). The caller
owns the stream. -/
def newStream (h : Host) (peer : PeerId) (protocols : List ProtocolId) :
    Async (Except Error (ProtocolId × Stream)) := do
  let some first := protocols.head?
    | return .error (.stream (.protocol "multistream: no protocol to propose"))
  if !(← (h.connected peer : BaseIO Bool)) then
    if let .error e ← h.dialPeer peer then return .error e
  let some e := SessionTable.live? (← (h.sessions.get : BaseIO (SessionTable Served))) peer
    | return .error (.stream (.closed "the session ended before the stream opened"))
  let some share ← (e.session.scope.reserveStream : BaseIO (Option Reservation))
    | return .error (.gated .resources)
  match ← (e.session.upgraded.session.openStream first).run with
  | .error err =>
    share.release
    return .error (.stream err)
  | .ok s =>
    match ← (negotiateStream .initiator s protocols).run with
    | .error err =>
      s.reset
      share.release
      return .error (.stream err)
    | .ok (id, s) =>
      -- The share returns when the stream is gone: at a reset, or once
      -- our close and the peer's end have both happened.
      let wroteEnd ← OnceRef.new false
      let readEnd ← OnceRef.new false
      let settle : BaseIO Unit := do
        if (← wroteEnd.get) && (← readEnd.get) then share.release
      return .ok (id, { s with
        read := do
          let r ← s.read
          unless r matches .ok (some _) do
            readEnd.set true
            settle
          return r
        close := do
          s.close
          wroteEnd.set true
          settle
        reset := do
          s.reset
          share.release })

end Host

end Libp2p.Host