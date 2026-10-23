import LeanP2P.Net.Transport
import LeanP2P.Conn.Security
import LeanP2P.Conn.Upgrade
import LeanP2P.Protocol.Multiselect
import LeanP2P.Crypto.Keys
import LeanP2P.Crypto.Multihash
import LeanP2P.Peer.Peerstore
import LeanP2P.Crypto.Bytes
/-!
# Host

The composition point: transport + upgrader + protocol dispatch. This
mirrors libp2p's Swarm/BasicHost split at spike scale.

Phase 4 (VECTOR_TEST_PLAN.md, steps 22-24):

- one `Upgrader`-shaped list of security protocols and muxers; inbound and
  outbound connections negotiate both with multistream-select;
- dial by address or by PeerId (addresses from the peerstore), verify the
  remote identity after the handshake, deduplicate sessions per peer;
- `addrs` reports the bound listen addrs with the `/p2p/` suffix;
- every task is owned (`TaskSet` / session task lists) and joined by
  `Host.close`, so the process can exit (Lean's RTS waits for tasks).
-/

namespace LeanP2P

structure HostConfig where
  key : Keys.PrivKey
  listenAddr : Multiaddr

structure Host where
  cfg : HostConfig
  id : PeerId
  transport : Transport
  securities : List SecurityProtocol
  muxers : List MuxChoice
  peerstore : Peerstore
  /-- live sessions by remote peer (connection dedup) -/
  conns : OnceRef (List (PeerId × Session))
  handlers : OnceRef (List (String × (Stream → IO Unit)))
  listeners : OnceRef (List Listener)
  /-- accepted connections still mid-upgrade (unauthenticated phase), so
  `close` can wake tasks parked in a handshake read on a silent peer -/
  pending : OnceRef (List (Nat × Connection))
  /-- set before closing: connections that finish upgrading during
  shutdown stop instead of registering and pumping forever -/
  closing : OnceRef Bool
  /-- source of unique session ids (dedup bookkeeping + pending ids) -/
  nextSid : OnceRef Nat
  tasks : TaskSet

def Host.new (cfg : HostConfig) (transport : Transport)
    (securities : List SecurityProtocol) (muxers : List MuxChoice) :
    IO (Option Host) := do
  let some pub ← cfg.key.publicKey | return none
  return (some
    { cfg := cfg
      id := PeerId.ofPublicKey pub
      transport := transport
      securities := securities
      muxers := muxers
      peerstore := ← Peerstore.new
      conns := ← OnceRef.new []
      handlers := ← OnceRef.new []
      listeners := ← OnceRef.new []
      pending := ← OnceRef.new []
      closing := ← OnceRef.new false
      nextSid := ← OnceRef.new 1
      tasks := ← TaskSet.new })

def Host.setStreamHandler (h : Host) (proto : String) (f : Stream → IO Unit) : IO Unit := do
  h.handlers.update fun hs => ((proto, f) :: hs, ())

/-- The listen addrs with the `/p2p/` peer-id suffix encapsulated
(identify semantics: one address per listener, `/p2p/<id>` appended). -/
def Host.addrs (h : Host) : IO (List Multiaddr) := do
  let ls ← h.listeners.get
  return ls.map fun l =>
    { l.addr with components := l.addr.components ++ [AddrComponent.p2p h.id.digestBytes false] }

/-- The peer id a trailing `/p2p/<id>` component addresses, if any. -/
def Host.addrPeer? (a : Multiaddr) : Option PeerId :=
  match a.components.getLast? with
  | some (.p2p mhash _) =>
      match Multihash.decode? mhash with
      | some mh => some { bytes := Bytes.ofNatList (Multihash.encode mh) }
      | none => none
  | _ => none

/-- The dialable prefix of `a` (everything before a trailing `/p2p/`). -/
def Host.addrBase (a : Multiaddr) : Multiaddr :=
  match a.components.getLast? with
  | some (.p2p _ _) => { a with components := a.components.dropLast }
  | _ => a

/-- Stamp a fresh unique session id (before dedup sees it). -/
def Host.stampSid (h : Host) (s : Session) : IO Session := do
  let sid ← h.nextSid.update fun n => (n + 1, n)
  pure { s with sid := sid }

/-- Spawn a tracked task (connection/stream handlers, serve loops). -/
def Host.spawn (h : Host) (act : IO Unit) : IO Unit :=
  h.tasks.spawn act

/-- Register a session unless one to that peer already exists; returns
the stored session and whether the given session was stored. -/
def Host.register (h : Host) (s : Session) : IO (Session × Bool) := do
  h.conns.update fun cs =>
    match cs.lookup s.remotePeer with
    | some old => (cs, (old, false))
    | none => (cs ++ [(s.remotePeer, s)], (s, true))

/-- The peer that initiated session `s`: us for our dials, the remote for
inbound connections. -/
def Host.initiatorOf (h : Host) (s : Session) : PeerId :=
  if s.inbound then s.remotePeer else h.id

/-- The window in which two opposite-direction connections count as a
simultaneous dial (both handshakes still ramping up). Each side measures
with its own clock, so decisions near the boundary can diverge; the
dead-session replacement below makes that self-healing (the side whose
connection lost sees it die and a redial replaces the dead entry). -/
def simulWindowMs : Nat := 30000

/-- Connection dedup. A dead session is always replaced (otherwise a peer
that restarted could never reconnect). A live session keeps its place -
except when an inbound/outbound pair raced: then both sides keep the
connection dialed by the peer with the smaller id, so the two decision
points converge on the same TCP connection (the spike's old rule dropped
the newer connection, which could leave both sides with nothing). A
later, non-racing connection never displaces a healthy session; go keeps
both and only resolves genuine races (known gap: a peer whose session we
still consider live cannot replace it until it is seen dead - the spike
has no keep-alive or yamux ping probe to notice earlier).

The dead probe needs IO, so probe and commit are separate steps; when
the occupant changed underneath the probe (a concurrent decide - exactly
the simultaneous-dial case), the full rule is re-evaluated against the
new occupant, bounded by a few retries. Returns the surviving session,
whether `newS` was stored, and the displaced session to shut down. -/
partial def Host.decide (h : Host) (newS : Session) :
    IO (Session × Bool × Option Session) := do
  let now ← IO.monoMsNow
  let newInit := Bytes.toNatList (Host.initiatorOf h newS).bytes
  let rec go (retries : Nat) :
      IO (Session × Bool × Option Session) := do
    let peek : Option Session ← h.conns.update fun cs => (cs, cs.lookup newS.remotePeer)
    let wantReplace ←
      match peek with
      | none => pure true
      | some old => do
        if ← old.mux.isDead then pure true
        else
          let raced := old.inbound != newS.inbound ∧ now - old.born ≤ simulWindowMs
          pure (raced ∧ newInit < Bytes.toNatList (Host.initiatorOf h old).bytes)
    let (stored, isNew, loser, moved) ← h.conns.update fun cs =>
      match cs.lookup newS.remotePeer with
      | none => (cs ++ [(newS.remotePeer, newS)], (newS, true, none, false))
      | some old =>
          let sameAsPeek : Bool :=
            (peek.map (fun o => o.sid == old.sid)).getD false
          if sameAsPeek then
            if wantReplace then
              (cs.filter (fun x => x.1 != newS.remotePeer)
                  ++ [(newS.remotePeer, newS)], (newS, true, some old, false))
            else
              (cs, (old, false, none, false))
          else
            -- a concurrent decide changed the entry between our probe
            -- and the commit: re-run the whole rule against the new
            -- occupant instead of silently first-commit-wins
            (cs, (old, false, none, true))
    if moved && retries > 0 then go (retries - 1)
    else pure (stored, isNew, loser)
  go 3

/-- Remove exactly `s` (by its unique host-assigned id) from the conns
cell. -/
def Host.pruneSession (h : Host) (s : Session) : IO Unit := do
  h.conns.update fun cs =>
    (cs.filter (fun x => x.1 != s.remotePeer ∨ x.2.sid != s.sid), ())

/-- The live session to a peer, if any. Dead sessions are pruned (only
the probed one - a concurrent decide may have stored a live successor),
so a reconnect (and dialPeer) never reuses one. -/
def Host.sessionOf (h : Host) (pid : PeerId) : IO (Option Session) := do
  match (← h.conns.get).lookup pid with
  | none => pure none
  | some s =>
    if ← s.mux.isDead then do
      Host.pruneSession h s
      pure none
    else pure (some s)

/-- Inbound stream: negotiate, then dispatch to the registered handler.
The negotiation reader's leftover bytes (data the peer coalesced past
the proposal reply - a lazy dialer's first message is already in flight)
are prepended to the stream handed to the handler, so a handler that
builds its own reader sees them instead of losing them. -/
partial def Host.handleStream (h : Host) (s : Stream) : IO Unit := do
  let supported := (← h.handlers.get).map (·.1)
  let reader ← BufReader.ofConn (s.conn)
  match ← Multiselect.selectResponder reader (s.conn) supported with
  | none => s.close
  | some proto =>
    match (← h.handlers.get).lookup proto with
    | none => s.close
    | some f => do
      let s' ← Stream.prependBytes s (← reader.buf.get)
      f s'

/-- Stream pump for one session: dispatch inbound streams to handlers. -/
partial def Host.acceptLoop (h : Host) (s : Session) : IO Unit := do
  match ← s.mux.acceptStream with
  | none => pure ()
  | some st =>
    h.spawn (h.handleStream st)
    h.acceptLoop s

/-- Inbound connection: upgrade (security + muxer negotiated as responder),
register, then pump inbound streams. Runs as its own task. The connection
stays on the `pending` list while it is unauthenticated, so `close` can
wake a handshake parked on a silent peer (the read deadline bounds the
wait either way). -/
partial def Host.handleConn (h : Host) (c : Connection) : IO Unit := do
  let pid ← h.nextSid.update fun n => (n + 1, n)
  h.pending.update fun cs => (cs ++ [(pid, c)], ())
  -- the unauthenticated phase is deadline-bounded: a raw TCP client that
  -- sends nothing fails the upgrade instead of parking the task forever.
  -- The timeout fires by closing the raw connection, so the session's
  -- connections (built on `c` itself) never inherit a read deadline.
  let up? ← Upgrade.withinDeadline upgradeTimeoutMs c.close
    (Upgrade.upgradeInbound h.securities h.muxers c)
  try
    match up? with
    | none => c.close
    | some sess => do
      if ← h.closing.get then
        sess.mux.shutdown   -- the host is shutting down: do not pump
      else do
        h.peerstore.addAddrs sess.remotePeer [sess.remoteAddr]
        let (_, isNew, loser) ← h.decide (← h.stampSid sess)
        match loser with
        | some old => old.mux.shutdown   -- our dial lost the race
        | none => pure ()
        unless isNew do
          sess.mux.shutdown   -- a session to this peer already exists
        h.acceptLoop sess
  finally
    h.pending.update fun cs => (cs.filter (fun x => x.1 != pid), ())

/-- Accept loop over the listener. -/
partial def Host.serveLoop (h : Host) (l : Listener) : IO Unit := do
  match ← l.accept with
  | none => pure ()
  | some c =>
    h.spawn (h.handleConn c)
    h.serveLoop l

/-- Start listening on the configured address; the serve loop is spawned
internally. -/
def Host.listen (h : Host) : IO (Option Listener) := do
  match ← h.transport.listen h.cfg.listenAddr with
  | none => return none
  | some l => do
    h.listeners.update fun ls => (ls ++ [l], ())
    h.spawn (h.serveLoop l)
    return (some l)

/-- Dial (or reuse a session) to `addr`; `expect` pins the identity the
handshake must authenticate. A trailing `/p2p/<id>` component on `addr`
is used as `expect` when none is given (and ignored for dialing), so
bootstrap-style addresses work directly. The new session's inbound-stream
pump is spawned here. -/
def Host.dial (h : Host) (addr : Multiaddr) (expect : Option PeerId) :
    IO (Option Session) := do
  let expect := match expect with
    | some pid => some pid
    | none => Host.addrPeer? addr
  let addr := Host.addrBase addr
  -- reuse: an existing session to the expected peer, or to this address
  let reuse? ←
    match expect with
    | some pid => h.sessionOf pid
    | none => do
      let cs ← h.conns.get
      match cs.find? (fun x => x.2.remoteAddr == addr) with
      | some x =>
        -- an address-keyed hit must still be alive; dead ones are pruned
        -- (identity-safe, as in sessionOf)
        if ← x.2.mux.isDead then do
          Host.pruneSession h x.2
          pure none
        else pure (some x.2)
      | none => pure none
  match reuse? with
  | some s => return (some s)
  | none => do
    match ← Upgrade.upgradeOutbound h.securities h.muxers h.transport addr expect with
    | none => return none
    | some sess =>
      h.peerstore.addAddrs sess.remotePeer [addr]
      let (stored, isNew, loser) ← h.decide (← h.stampSid sess)
      match loser with
      | some old => old.mux.shutdown   -- displaced by the race winner
      | none => pure ()
      if isNew then do
        h.spawn (h.acceptLoop sess)
        return (some sess)
      else do
        sess.mux.shutdown    -- lost a dedup race: drop our connection
        return (some stored)

/-- Dial by PeerId: addresses come from the peerstore, and the handshake
must authenticate the expected identity. -/
def Host.dialPeer (h : Host) (pid : PeerId) : IO (Option Session) := do
  match ← h.sessionOf pid with
  | some s => return (some s)
  | none => do
    let rec go : List Multiaddr → IO (Option Session)
      | [] => return none
      | a :: rest => do
        match ← h.dial a (some pid) with
        | some s => return (some s)
        | none => go rest
    go (← h.peerstore.addrsOf pid)

/-- Open a negotiated stream in a session and run the multiselect dialer
(lazy mode) for `proto`. Bytes the reply coalesced with (the peer may
already be streaming its first message) ride along on the returned
stream: they are prepended to its reads, so nothing negotiated away is
lost. -/
def Host.openProto (sess : Session) (proto : String) : IO (Option Stream) := do
  let some s ← sess.mux.openStream proto | return none
  let reader ← BufReader.ofConn (s.conn)
  match ← Multiselect.selectInitiatorLazy reader (s.conn) proto with
  | none =>
    s.close
    return none
  | some _ => some <$> Stream.prependBytes s (← reader.buf.get)

/-- Dial (or reuse) and negotiate `proto` over a fresh stream. -/
def Host.newStream (h : Host) (addr : Multiaddr) (proto : String) :
    IO (Option Stream) := do
  match ← h.dial addr none with
  | none => return none
  | some sess => Host.openProto sess proto

/-- Dial by PeerId (or reuse) and negotiate `proto` over a fresh stream. -/
def Host.newStreamTo (h : Host) (pid : PeerId) (proto : String) :
    IO (Option Stream) := do
  match ← h.dialPeer pid with
  | none => return none
  | some sess => Host.openProto sess proto

/-- Close listeners and sessions, then join every owned task (serve loops,
connection handlers, stream handlers and muxer frame pumps). Connections
still mid-upgrade are closed first, so a task parked in a handshake read
on a silent peer wakes with EOF instead of hanging the join (the read
deadline is only the backstop). -/
def Host.close (h : Host) : IO Unit := do
  h.closing.set true
  (← h.listeners.get).forM fun l => l.close
  -- wake every task parked in an unauthenticated handshake (EOF)
  for (_, c) in ← h.pending.get do
    c.close
  for (_, s) in ← h.conns.get do
    s.mux.shutdown
  -- session frame pumps exit once their pipes/connections are closed
  for (_, s) in ← h.conns.get do
    s.mux.tasks.joinAll
  h.tasks.joinAll

end LeanP2P
