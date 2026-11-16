import Std.Data.HashMap
import Tests.Support
import Conc
import Streams
import Multiformats
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Security
import Libp2p.Mux
import Libp2p.Negotiate
import Libp2p.Host

/-!
# Host suite (unit W5.6)

The checks of `packages/libp2p/host/docs/PLAN.md`.

Unit 1a: the dedup rule, the session table's liveness, the handler
table, the peerstore, and the `Host.Error` lines. Every check runs the
pure update functions, by value or under an `OnceRef`, with no
connection in the loop. The session handle of a table entry is a `Nat`
here, since the rule never reads it.

Unit 1b: hosts over the test values of root §3.1 (PRINCIPLES 1.4): the
sim transport, the fixed-key test value `Noise.fixedKeyProtocol`, and
a test clock that drives the upgrade deadline, so no check waits on the
wall clock. Each host offers `[Mux.yamux, Mux.mplex]`, in the order
of the consensus networking spec, so two hosts agree on yamux. A plain
upgrader that offers mplex alone reaches the host over mplex. Each host
hands its failures to a channel that the check reads.
-/

set_option autoImplicit false

namespace Tests

open Conc Multiformats Libp2p.Identity Libp2p.Core Libp2p.Host

/-! ## Helpers -/

/-- A multiaddr from its text form. -/
private def ma (s : String) : IO Multiaddr := do
  match Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- The smaller and the larger of two test peers: the inlined ids of
the one-byte keys `1` and `2`. Their binary forms are `[0x00, 0x01, 1]`
and `[0x00, 0x01, 2]`, so `small` orders first. The size bound
`1 ≤ 42` holds by evaluation. -/
private def small : PeerId := PeerId.inline (ByteArray.mk #[1]) (by decide)
private def large : PeerId := PeerId.inline (ByteArray.mk #[2]) (by decide)

/-- A live table entry. -/
private def entry (id : Nat) (role : Role) (bornMs : Nat) : Entry Nat :=
  { id, role, bornMs, live := true, session := id }

/-- The session number of the entry of `peer`, when it has one. -/
private def holder (t : SessionTable Nat) (peer : PeerId) : Option Nat :=
  (t.get? peer).map (·.id)

/-- True when the decision committed the candidate and displaced the
session `id` (`none`: displaced nothing). -/
private def committedOver (d : Decision Nat) (id : Option Nat) : Bool :=
  match d with
  | .commit displaced => displaced.map (·.id) == id
  | .keep _ => false

/-- True when the decision kept the standing session `id`. -/
private def keptId (d : Decision Nat) (id : Nat) : Bool :=
  match d with
  | .keep s => s.id == id
  | .commit _ => false

/-! ## Dedup -/

/-- The rule of the package ARCHITECTURE, contract 2, run by value. -/
private def dedupChecks (r : Runner) : IO Unit := do
  r.check "the binary order puts the smaller test peer first" (comparePeers small large == .lt)

  -- An absent slot, and a dead standing session, take the candidate.
  let (d, t) := dedup small large (entry 1 .initiator 0) {}
  r.check "an empty slot takes the candidate" (committedOver d none && holder t large == some 1)
  let dead : SessionTable Nat := ({} : SessionTable Nat).insert large { entry 1 .initiator 0 with live := false }
  let (d, t) := dedup small large (entry 2 .initiator 10) dead
  r.check "a dead standing session makes room" (committedOver d none && holder t large == some 2)

  -- A race inside the window: the connection the larger id dialed
  -- loses. Each case runs on the side that holds the larger id and on
  -- the side that holds the smaller one, and the standing session
  -- runs first in one direction and then in the other.
  let born := 1000
  let inWindow := born + simulWindowMs - 1
  -- We hold the smaller id. The peer (larger) dialed the standing
  -- session, so it loses to our new dial.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .responder born)
  let (d, t) := dedup small large (entry 2 .initiator inWindow) standing
  r.check "smaller side: our dial beats the larger peer's dial" (committedOver d (some 1) && holder t large == some 2)
  -- We hold the smaller id, and we dialed the standing session. The
  -- larger peer's dial arrives and loses.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .initiator born)
  let (d, t) := dedup small large (entry 2 .responder inWindow) standing
  r.check "smaller side: the larger peer's dial loses to ours" (keptId d 1 && holder t large == some 1)
  -- We hold the larger id, and we dialed the standing session. The
  -- smaller peer's dial arrives and wins.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert small (entry 1 .initiator born)
  let (d, t) := dedup large small (entry 2 .responder inWindow) standing
  r.check "larger side: the smaller peer's dial beats ours" (committedOver d (some 1) && holder t small == some 2)
  -- We hold the larger id. The smaller peer dialed the standing
  -- session, and our own dial loses to it.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert small (entry 1 .responder born)
  let (d, t) := dedup large small (entry 2 .initiator inWindow) standing
  r.check "larger side: our dial loses to the smaller peer's" (keptId d 1 && holder t small == some 1)

  -- The window edge: a candidate born `simulWindowMs` after the
  -- standing session is outside it, and the standing session stays,
  -- even when the race rule would have dropped it.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .responder born)
  let (d, _) := dedup small large (entry 2 .initiator (born + simulWindowMs)) standing
  r.check "outside the window the live standing session stays" (keptId d 1)
  -- The same direction is no race: a second dial of ours keeps the
  -- first session, inside the window too.
  let standing : SessionTable Nat := ({} : SessionTable Nat).insert large (entry 1 .initiator born)
  let (d, t) := dedup small large (entry 2 .initiator inWindow) standing
  r.check "a second dial in the same direction keeps the first" (keptId d 1 && holder t large == some 1)

  -- Both sides at once. Peer `small` dialed connection A, and peer
  -- `large` dialed connection B. Each side committed one first; the
  -- other then arrives as the candidate. Both keep A, the connection
  -- that the smaller id dialed.
  for aFirstOnSmall in [true, false] do
    for aFirstOnLarge in [true, false] do
      -- On `small`, A is ours (`.initiator`), and B is the peer's.
      let (firstS, secondS) :=
        if aFirstOnSmall then (entry 0 .initiator born, entry 1 .responder inWindow)
        else (entry 1 .responder born, entry 0 .initiator inWindow)
      let (_, ts) := dedup small large firstS {}
      let (_, ts) := dedup small large secondS ts
      -- On `large`, A is the peer's (`.responder`), and B is ours.
      let (firstL, secondL) :=
        if aFirstOnLarge then (entry 0 .responder born, entry 1 .initiator inWindow)
        else (entry 1 .initiator born, entry 0 .responder inWindow)
      let (_, tl) := dedup large small firstL {}
      let (_, tl) := dedup large small secondL tl
      r.check s!"both sides keep the smaller id's dial (A first on small: {aFirstOnSmall}, on large: {aFirstOnLarge})"
        (holder ts large == some 0 && holder tl small == some 0)

/-- Many decisions over one peer under one cell: each runs as its own
task, through `OnceRef.updateGet`, and the table ends with exactly the
survivor the decisions name (PRINCIPLES 3.3). -/
private def concurrentDedupChecks (r : Runner) : Async Unit := do
  -- Sixteen dials of ours to one peer, all in the same direction: one
  -- commits, the rest keep it, and no update is lost.
  let cell : OnceRef (SessionTable Nat) ← OnceRef.new {}
  let answers : OnceRef (List (Decision Nat)) ← OnceRef.new []
  let ts ← TaskSet.new
  for i in [0:16] do
    ts.spawn do
      let d ← (cell.updateGet (dedup small large (entry i .initiator 0)) : BaseIO (Decision Nat))
      answers.update (d :: ·)
  ts.joinAll
  let ds ← (answers.get : BaseIO (List (Decision Nat)))
  let t ← (cell.get : BaseIO (SessionTable Nat))
  let winners := ds.filter (·.committed)
  r.check "sixteen same-direction dials: one commits" (winners.length == 1)
  r.check "sixteen same-direction dials: the rest keep the winner"
    (ds.all fun d => match d, holder t large with
      | .keep s, some w => s.id == w
      | .commit none, _ => true
      | _, _ => false)

  -- Two opposite dials inside the window, in either order: the table
  -- ends with the smaller id's dial, and the decisions agree with it.
  for _ in [0:8] do
    let cell : OnceRef (SessionTable Nat) ← OnceRef.new {}
    let answers : OnceRef (List (Decision Nat)) ← OnceRef.new []
    let ts ← TaskSet.new
    -- On `small`, our dial is the smaller id's dial.
    for (i, role) in [(0, Role.initiator), (1, Role.responder)] do
      ts.spawn do
        let d ← (cell.updateGet (dedup small large (entry i role 0)) : BaseIO (Decision Nat))
        answers.update (d :: ·)
    ts.joinAll
    let t ← (cell.get : BaseIO (SessionTable Nat))
    let ds ← (answers.get : BaseIO (List (Decision Nat)))
    r.check "two opposite dials: the smaller id's dial survives" (holder t large == some 0)
    -- The peer's dial (1) is displaced when it ran first, and kept out
    -- when it ran second; our dial (0) never loses.
    r.check "two opposite dials: the decisions name the survivor"
      (ds.all fun d => match d with
        | .keep s => s.id == 0
        | .commit (some s) => s.id == 1
        | .commit none => true)

/-- Liveness is a table field (contract 3): a session that exits marks
its entry dead through the cell, and the next decision reads it. -/
private def livenessChecks (r : Runner) : Async Unit := do
  let cell : OnceRef (SessionTable Nat) ← OnceRef.new {}
  discard <| (cell.updateGet (dedup small large (entry 1 .initiator 0)) : BaseIO (Decision Nat))
  -- The session loop runs as a task and marks its exit on the way out.
  let ts ← TaskSet.new
  ts.spawn do cell.update (SessionTable.markDead large 1)
  ts.joinAll
  let t ← (cell.get : BaseIO (SessionTable Nat))
  r.check "an exited session reads as dead" ((t.get? large).any (!·.live) && (t.live? large).isNone)
  -- A dial outside any race takes the slot of the dead session.
  let d ← (cell.updateGet (dedup small large (entry 2 .initiator 5)) : BaseIO (Decision Nat))
  r.check "the next decision replaces the dead session" (committedOver d none)
  -- The late exit of the replaced session leaves its successor live.
  cell.update (SessionTable.markDead large 1)
  let t ← (cell.get : BaseIO (SessionTable Nat))
  r.check "a stale exit leaves the successor live" ((t.live? large).any (·.id == 2))
  r.check "the live entries list the successor"
    ((SessionTable.liveEntries t).map (·.2.id) == [2])

/-! ## The handler table -/

/-- A handler that half-closes its stream. -/
private def closer (id : ProtocolId) : StreamHandler where
  id := id
  handle := fun _ s => s.close

private def handlerChecks (r : Runner) : Async Unit := do
  let ping : ProtocolId := ⟨"/ipfs/ping/1.0.0"⟩
  let ident : ProtocolId := ⟨"/ipfs/id/1.0.0"⟩
  -- A handler set under the cell is visible to the next read.
  let cell : OnceRef Handlers ← OnceRef.new {}
  let ts ← TaskSet.new
  for h in [closer ping, closer ident] do
    ts.spawn do cell.update (Handlers.set h)
  ts.joinAll
  let t ← (cell.get : BaseIO Handlers)
  r.check "a set handler is found by its id" ((t.find? ping).any (·.id == ping))
  r.check "an unknown id finds no handler" (t.find? ⟨"/ipfs/ping/2.0.0"⟩).isNone
  r.check "the table lists its ids in text order" (Handlers.ids t == [ident, ping])
  let t := Handlers.set (closer ping) t
  r.check "a second set under one id replaces the first" (Handlers.ids t == [ident, ping])

/-! ## The peerstore -/

private def peerstoreChecks (r : Runner) : Async Unit := do
  let a1 ← ma "/ip4/10.0.0.1/tcp/4001"
  let a2 ← ma "/ip6/::1/tcp/4002"
  let a3 ← ma "/memory/3"
  -- Addresses round-trip, in the order they arrived.
  let s := Peerstore.addAddrs large [a1, a2] {}
  r.check "the peerstore returns the added addresses" (Peerstore.addrsOf s large == [a1, a2])
  r.check "an unknown peer has no addresses" (Peerstore.addrsOf s small).isEmpty
  -- A redial's re-add of the same address grows nothing.
  let s' := Peerstore.addAddrs large [a2, a1] s
  r.check "a re-add leaves the set unchanged" (Peerstore.addrsOf s' large == [a1, a2])
  let s' := Peerstore.addAddrs large [a3, a3] s'
  r.check "a new address joins once" (Peerstore.addrsOf s' large == [a1, a2, a3])

  -- N tasks add to one store under the cell: every address lands, and
  -- none twice (the base/conc milestone shape).
  let cell : OnceRef Peerstore ← OnceRef.new {}
  let addrs ← (List.range 32).mapM fun i => ma s!"/ip4/10.0.0.{i}/tcp/4001"
  let ts ← TaskSet.new
  for a in addrs do
    -- Each address goes in twice, from two tasks.
    for _ in [0:2] do
      ts.spawn do cell.update (Peerstore.addAddrs large [a])
  ts.joinAll
  let got := Peerstore.addrsOf (← (cell.get : BaseIO Peerstore)) large
  r.check "concurrent adds keep every address" (addrs.all got.contains)
  r.check "concurrent adds keep each address once" (got.length == addrs.length)

/-! ## `Host.Error` -/

private def errorChecks (r : Runner) : IO Unit := do
  let a ← ma "/memory/7"
  let arms : List (Libp2p.Host.Error × String) :=
    [(.upgrade (.timeout "30000 ms"), "upgrade failed: timeout: 30000 ms"),
     (.session (.protocol "bad frame"), "session failed: protocol error: bad frame"),
     (.stream (.closed "reset"), "stream failed: closed: reset"),
     (.gated .secured, "refused by policy at the secured checkpoint"),
     (.noAddresses large, s!"no address for peer {large}"),
     (.noTransport a, "no transport handles /memory/7"),
     (.unreachable a, "nobody listens at /memory/7"),
     (.dialSelf, "a dial to our own peer id"),
     (.closing, "the host is closing")]
  for (e, line) in arms do
    r.check s!"Host.Error renders {line}" (toString e == line)

/-! ## Unit 1b: hosts over the sim -/

section Swarm

open Streams Libp2p.Security
open Libp2p.Host (Host Config Failure Stage)

/-- `n` bytes of the value `v`. -/
private def fill (n : Nat) (v : UInt8) : ByteArray := ⟨Array.replicate n v⟩

/-- A Noise configuration from an Ed25519 identity byte. The static key
byte follows from it. -/
private def cfgOf (idByte : UInt8) : Async Noise.Config := do
  let .ok identity := PrivKey.ofData? .ed25519 (fill 32 idByte)
    | throw <| IO.userError "test identity does not build"
  let some static := Noise.Bytes32.ofByteArray? (fill 32 (idByte + 100))
    | throw <| IO.userError "test static key is not 32 bytes"
  return { identity, static }

/-- The fixed-key Noise value of the identity byte `idByte`: its
ephemeral keys come from an `Rng` seeded with 32 copies of
`idByte + 50` (root §3.1). -/
private def noiseOf (idByte : UInt8) : Async SecurityProtocol :=
  return Noise.fixedKeyProtocol (← cfgOf idByte) (fill 32 (idByte + 50))

/-- The echo protocol of the suite. The `/test/` prefix keeps it apart
from every real id. -/
private def echoId : ProtocolId := ⟨"/test/echo"⟩

/-- A protocol whose handler fails at once. -/
private def failId : ProtocolId := ⟨"/test/fail"⟩

/-- An id no host serves. -/
private def unknownId : ProtocolId := ⟨"/test/unknown"⟩

/-- Read until the end of the stream, or a reset. -/
private def readAll (s : Stream) : Async ByteArray := do
  let mut acc := ByteArray.empty
  repeat
    match ← s.read with
    | .ok (some b) => acc := acc ++ b
    | _ => break
  return acc

/-- The echo handler: read to the end, write it back, close. -/
private def echoHandler : StreamHandler where
  id := echoId
  handle _ s := do
    let got ← readAll s
    discard <| s.write got
    s.close

/-- The id of the handler that records its context. -/
private def ctxId : ProtocolId := ⟨"/test/ctx"⟩

/-- The failing handler. -/
private def failHandler : StreamHandler where
  id := failId
  handle _ _ := throw (.protocol "the test handler fails")

/-- A host of the suite on `net`, its peer id, and the channel its
failures arrive on. -/
private def mkHost (net : Sim.Net) (idByte : UInt8) (tc : TestClock)
    (gater : ConnectionGater := Policy.permissiveGater)
    (resources : ResourceManager := Policy.unlimited) :
    Async (Host × Chan Failure) := do
  let cfg ← cfgOf idByte
  let failures : Chan Failure ← Chan.new 16
  let noise ← noiseOf idByte
  let some localPeer := (cfg.identity.toPublic.bind PeerId.ofPubKey).toOption
    | throw <| IO.userError "test peer id does not build"
  let config : Config := {
    identity := cfg.identity
    transports := [net.transport]
    -- The sim value of the secured seam takes the `quic-v1` addresses of
    -- the net, so every host of the suite has a secured path too.
    securedTransports := [Libp2p.Negotiate.securedOver net.transport Policy.isQuic localPeer
      [noise] [Libp2p.Mux.yamux] tc.clock]
    security := [noise]
    muxers := [Libp2p.Mux.yamux, Libp2p.Mux.mplex]
    handlers := [echoHandler, failHandler]
    gater
    resources
    clock := tc.clock
    onFailure := fun f => discard (failures.trySend f) }
  match ← (Host.new config : BaseIO _) with
  | .ok h => return (h, failures)
  | .error _ => throw <| IO.userError "test host does not build"

/-- The address with `/p2p/<peer>` after it. -/
private def withPeer (a : Multiaddr) (p : PeerId) : Async Multiaddr := do
  match a.encapsulate (← ma s!"/p2p/{p}") with
  | .ok full => return full
  | .error _ => throw <| IO.userError "the /p2p address does not build"

/-- Start a listener, or fail the run. -/
private def listenOn (h : Host) (text : String) : Async Multiaddr := do
  match ← h.startListening (← ma text) with
  | .ok a => return a
  | .error e => throw <| IO.userError s!"listen failed: {e}"

/-- One echo round trip from `h` to `peer`: the stream negotiates
`echoId`, the bytes come back, and the stream ends. -/
private def echoOnce (h : Host) (peer : PeerId) (payload : String) : Async Bool := do
  match ← h.newStream peer [echoId] with
  | .error _ => return false
  | .ok (id, s) =>
    discard <| s.write payload.toUTF8
    s.close
    return id == echoId && (← readAll s) == payload.toUTF8

/-- The pipeline in both directions: a dial with `/p2p`, an echo each
way, a redial that reuses the session, and an identity mismatch. -/
private def pipelineChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, _) ← mkHost net 1 tc
  let (b, _) ← mkHost net 2 tc
  let addrA ← listenOn a "/memory/101"
  let addrB ← listenOn b "/memory/102"
  -- B dials A by its address and peer id.
  match ← b.dial (← withPeer addrA a.localPeer) with
  | .ok p => r.check "host: a dial proves the listener's peer id" (p == a.localPeer)
  | .error e => r.check s!"host: a dial succeeds ({e})" false
  r.check "host: the dialer serves the session" (← (b.connected a.localPeer : BaseIO Bool))
  r.check "host: the dialer's stream echoes" (← echoOnce b a.localPeer "ping")
  -- The listener committed the session too, and it opens streams back.
  r.check "host: the listener's stream echoes" (← echoOnce a b.localPeer "pong")
  -- A served stream gets the session's context: the proved peer, and
  -- the connection's remote address. B dialed, so B's connection names
  -- `addrA` as its remote end. A's connection names the sim port of
  -- B's dial.
  let seenA : Chan StreamContext ← Chan.new 1
  let seenB : Chan StreamContext ← Chan.new 1
  let recorder (seen : Chan StreamContext) : StreamHandler :=
    { id := ctxId, handle := fun ctx s => do discard <| seen.send ctx; s.close }
  a.setHandler (recorder seenA)
  b.setHandler (recorder seenB)
  discard <| b.newStream a.localPeer [ctxId]
  discard <| a.newStream b.localPeer [ctxId]
  match ← seenA.recv, ← seenB.recv with
  | some ca, some cb =>
    r.check "host: the handler context names the proved peer"
      (ca.remotePeer == b.localPeer && cb.remotePeer == a.localPeer)
    r.check "host: the dialer's handler context names the listener's address"
      (cb.remoteAddr == addrA && ca.remoteAddr != addrA)
  | _, _ => r.check "host: both handlers saw a context" false
  -- A redial reuses the live session, and the peerstore grows nothing.
  match ← b.dial (← withPeer addrA a.localPeer) with
  | .ok p => r.check "host: a redial reuses the session" (p == a.localPeer)
  | .error e => r.check s!"host: a redial succeeds ({e})" false
  r.check "host: the dial stored the address once"
    ((← (b.addrsOf a.localPeer : BaseIO (List Multiaddr))) == [addrA])
  -- A dial that expects another peer fails at the identity check.
  let (c, _) ← mkHost net 3 tc
  match ← c.dial addrB (peer := some a.localPeer) with
  | .error (.upgrade (.authentication _)) =>
    r.check "host: an identity mismatch fails with authentication" true
  | _ => r.check "host: an identity mismatch fails with authentication" false
  r.check "host: the mismatched dial leaves no session" !(← (c.connected b.localPeer : BaseIO Bool))
  c.close
  b.close
  a.close
  tc.close

/-- The host's own answers: a dial to itself, a peer with no address,
an address with no transport part, an unknown protocol, a failing
handler, and the calls after `close`. -/
private def answerChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, failsA) ← mkHost net 4 tc
  let (b, _) ← mkHost net 5 tc
  let addrA ← listenOn a "/memory/111"
  r.check "host: a dial to our own id fails"
    ((← b.dial addrA (peer := some b.localPeer)) matches .error .dialSelf)
  r.check "host: a peer with no address fails"
    ((← b.dialPeer a.localPeer) matches .error (.noAddresses _))
  r.check "host: a /p2p address alone has no transport"
    ((← b.dial (← ma s!"/p2p/{a.localPeer}")) matches .error (.noTransport _))
  -- `dialPeer` walks the peerstore.
  b.addAddrs a.localPeer [addrA]
  r.check "host: dialPeer dials the peerstore address"
    ((← b.dialPeer a.localPeer) matches .ok _)
  -- The host answers `na` to an unknown protocol, and the session stays.
  r.check "host: an unknown protocol fails the stream"
    ((← b.newStream a.localPeer [unknownId]) matches .error (.stream _))
  r.check "host: the session stays after an unknown protocol"
    (← echoOnce b a.localPeer "still here")
  -- A handler set on a running host serves the next stream.
  (a.setHandler { echoHandler with id := unknownId } : BaseIO Unit)
  r.check "host: a handler set at runtime serves the next stream"
    ((← b.newStream a.localPeer [unknownId]) matches .ok _)
  -- A failing handler resets the stream and reaches A's owner. The
  -- session stays. A sends its reset right after its negotiation reply,
  -- and a reset may drop the bytes in flight (`Streams.Error.reset`).
  -- So B sees the reset in its first read. Or the reset comes before B
  -- reads the reply, and B's negotiation ends with `closed`.
  let resetSeen ← match ← b.newStream a.localPeer [failId] with
    | .error (.stream (.closed _)) => pure true
    | .error _ => pure false
    | .ok (_, s) => pure ((← s.read) matches .error .reset)
  r.check "host: a handler failure resets the stream" resetSeen
  match ← failsA.recv with
  | some f =>
    r.check "host: a handler failure reaches the owner"
      (f.peer == some b.localPeer && f.protocol == some failId &&
        f.error matches .stream (.protocol _))
  | none => r.check "host: a handler failure reaches the owner" false
  r.check "host: the session stays after a handler failure"
    (← echoOnce b a.localPeer "and here")
  b.close
  a.close
  r.check "host: a dial after close fails with closing"
    ((← b.dial addrA) matches .error .closing)
  r.check "host: a listen after close fails with closing"
    ((← a.startListening (← ma "/memory/112")) matches .error .closing)
  tc.close

/-- A gater that passes the dial and the accept, and refuses every
proved peer: only the secured checkpoint answers no. -/
private def securedOnlyGater : ConnectionGater :=
  { Policy.permissiveGater with allowSecured := fun _ _ _ _ => pure false }

/-- The policy doubles. A denying gater refuses a dial and an accepted
connection. The permissive gater passes both, in the other checks. A
gater that refuses at the secured checkpoint refuses after the
handshake, and the scope and the secure connection close with it. -/
private def policyChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (open_, _) ← mkHost net 6 tc
  let (shut, failsShut) ← mkHost net 7 tc (gater := Policy.denyingGater)
  let addrOpen ← listenOn open_ "/memory/121"
  let addrShut ← listenOn shut "/memory/122"
  r.check "host: a denying gater refuses a dial"
    ((← shut.dial addrOpen) matches .error (.gated .dial))
  -- The refused inbound connection closes before any byte moves. The
  -- dialer meets the close as the end of its read (`closed`), or as a
  -- failed write, which is a fault (`Connection.write`, §3.5). The
  -- order of its write and the close decides which.
  let refused ← try
      pure ((← open_.dial addrShut) matches .error (.upgrade (.closed _)))
    catch _ => pure true
  r.check "host: a denying gater refuses an inbound connection" refused
  r.check "host: the refusal is no failure" (← (failsShut.tryRecv : BaseIO _)).isNone
  r.check "host: the refused inbound peer has no session"
    !(← (shut.connected open_.localPeer : BaseIO Bool))
  -- The secured checkpoint: the dial and the handshake pass, and the
  -- checkpoint refuses the proved peer before the muxer stage.
  let (picky, failsPicky) ← mkHost net 13 tc (gater := securedOnlyGater)
  r.check "host: the secured checkpoint refuses an outbound peer"
    ((← picky.dial addrOpen) matches .error (.gated .secured))
  r.check "host: the outbound secured refusal leaves no session"
    !(← (picky.connected open_.localPeer : BaseIO Bool))
  let addrPicky ← listenOn picky "/memory/123"
  -- The dialer's handshake completes, then its muxer stage meets the
  -- close. A failed write is a fault (§3.5), as above.
  let refusedIn ← try
      pure ((← open_.dial addrPicky) matches .error (.upgrade _))
    catch _ => pure true
  r.check "host: the secured checkpoint refuses an inbound peer" refusedIn
  r.check "host: the secured refusal is no failure" (← (failsPicky.tryRecv : BaseIO _)).isNone
  r.check "host: the inbound secured refusal leaves no session"
    !(← (picky.connected open_.localPeer : BaseIO Bool))
  picky.close
  open_.close
  shut.close
  tc.close

/-- True when `raw` reaches its end within eight reads. The host's
responder writes its multistream header before it reads, as go's
listener does (`Negotiate.negotiate`). So a raw peer can read that
header before the end. A peer that sends past the bound counts as no
end. -/
private def endsSoon (raw : Connection) : Async Bool := do
  for _ in [0:8] do
    if (← raw.read).isNone then return true
  return false

/-- The silent peer, at host level (PRINCIPLES 5.4): a raw connection
that sends nothing parks the inbound upgrade. The deadline fails it,
and the failure reaches the owner. In a second run, `close` reaches
the parked upgrade through the pending list, and every join returns. -/
private def silentPeerChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, failsA) ← mkHost net 8 tc
  let addrA ← listenOn a "/memory/131"
  let some raw ← net.transport.dial addrA | throw <| IO.userError "raw dial failed"
  -- The upgrade arms its deadline before its first read parks.
  discard tc.nextTimer
  tc.advance Streams.unauthDeadlineMs
  match ← failsA.recv with
  | some f =>
    r.check "host: a silent peer fails at the deadline"
      (f.peer.isNone && f.error matches .upgrade (.timeout _))
  | none => r.check "host: a silent peer fails at the deadline" false
  r.check "host: the deadline closed the silent connection" (← endsSoon raw)
  -- A second silent peer, and `close` before the deadline.
  let some raw ← net.transport.dial addrA | throw <| IO.userError "raw dial failed"
  discard tc.nextTimer
  a.close
  r.check "host: close reaches a parked upgrade, and returns" (← endsSoon raw)
  tc.close

/-- The shutdown order (§5.5): the stages run in sequence, and every
join returns, with a listener whose accept parks, a live session, and
a pending connection. -/
private def shutdownChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, _) ← mkHost net 9 tc
  let (b, _) ← mkHost net 10 tc
  let addrA ← listenOn a "/memory/141"
  discard <| listenOn a "/memory/142"
  discard <| b.dial addrA
  let some raw ← net.transport.dial addrA | throw <| IO.userError "raw dial failed"
  let stages : OnceRef (List Stage) ← OnceRef.new []
  a.close (onStage := fun s => stages.update (· ++ [s]))
  r.check "host: the shutdown runs the stages of §5.5 in order"
    ((← (stages.get : BaseIO (List Stage))) ==
      [.flag, .listeners, .pending, .sessions, .sessionLoops, .hostTasks])
  r.check "host: the shutdown closed the pending connection" (← endsSoon raw)
  r.check "host: a closed listener refuses a dial"
    ((← b.dial addrA (peer := none)) matches .error _)
  -- A second close finds nothing left, and returns.
  a.close
  b.close
  tc.close

/-- The leftover hand-over on a served stream (§4.7, §5.6). A peer
writes its stream header, its proposal, and data in one write. The
handler gets the data in its first read. The peer runs the plain
upgrader of `libp2p/negotiate`, so the host's listen path meets a peer
that is no host. -/
private def handOverChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, _) ← mkHost net 11 tc
  let addrA ← listenOn a "/memory/151"
  let noise ← noiseOf 12
  let some conn ← net.transport.dial addrA | throw <| IO.userError "dial failed"
  match ← (Libp2p.Negotiate.upgradeWith tc.clock .initiator conn .empty (some a.localPeer)
      [noise] [Libp2p.Mux.yamux]).run with
  | .error e => r.check s!"host: a plain upgrader reaches the host ({e})" false
  | .ok (session, _) =>
    match ← (session.openStream echoId).run with
    | .error e => r.check s!"host: the stream opens ({e})" false
    | .ok s =>
      let msg (t : String) : ByteArray := Bytes.ofNatList (Libp2p.Negotiate.encodeText t)
      discard <| s.write (msg "/multistream/1.0.0" ++ msg "/test/echo" ++ "coalesced".toUTF8)
      s.close
      -- The echo handler answers the header and the id, then the bytes.
      let back ← readAll s
      r.check "host: the bytes behind the proposal reach the handler"
        (back == msg "/multistream/1.0.0" ++ msg "/test/echo" ++ "coalesced".toUTF8)
    discard session.close.toBaseIO
    discard session.join.run
  a.close
  tc.close

/-- The second muxer of the host (root PLAN W5.10). A peer that
offers mplex alone gets mplex from the host, which offers yamux first,
and a stream carries bytes over it. -/
private def mplexChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, _) ← mkHost net 13 tc
  let addrA ← listenOn a "/memory/161"
  let noise ← noiseOf 14
  let some conn ← net.transport.dial addrA | throw <| IO.userError "dial failed"
  match ← (Libp2p.Negotiate.upgradeWith tc.clock .initiator conn .empty (some a.localPeer)
      [noise] [Libp2p.Mux.mplex]).run with
  | .error e => r.check s!"host: a peer that offers mplex alone upgrades ({e})" false
  | .ok (session, _) =>
    r.check "host: a peer that offers mplex alone upgrades" true
    match ← (session.openStream echoId).run with
    | .error e => r.check s!"host: a stream opens over mplex ({e})" false
    | .ok s =>
      let msg (t : String) : ByteArray := Bytes.ofNatList (Libp2p.Negotiate.encodeText t)
      discard <| s.write (msg "/multistream/1.0.0" ++ msg "/test/echo" ++ "over mplex".toUTF8)
      s.close
      let back ← readAll s
      r.check "host: the echo comes back over mplex"
        (back == msg "/multistream/1.0.0" ++ msg "/test/echo" ++ "over mplex".toUTF8)
    discard session.close.toBaseIO
    discard session.join.run
  a.close
  tc.close

/-! ## The secured paths

Every host of the suite holds the sim value of the secured seam
(`Libp2p.Negotiate.securedOver`, root ARCHITECTURE §3.1) for the
`quic-v1` addresses of the net, beside the sim transport for the rest.
So the host's secured paths run with no socket (PRINCIPLES 1.4), the
same paths a QUIC connection takes. -/

/-- A resource manager that limits nothing and counts the scopes it
opened and the scopes released, each release once. -/
private def countingResources (opened released : OnceRef Nat) : ResourceManager where
  openConnection _ _ _ := do
    opened.update (· + 1)
    let once ← OnceRef.new false
    return some {
      setPeer := fun _ => pure true
      reserveStream := pure (some { release := pure () })
      reserveMemory := fun _ => pure (some { release := pure () })
      release := do
        if !(← once.updateGet fun d => (d, true)) then released.update (· + 1) }

/-- The secured pipeline: a dial to a `quic-v1` address takes the
secured path, proves the peer, and serves streams both ways. A peer
with a TCP address and a QUIC address in the peerstore is dialed over
QUIC (`Policy.quicFirst`): the stream context of the dialer names the
QUIC address. A dial over both paths at once ends with the peer served,
whichever session the dedup keeps. -/
private def securedChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, _) ← mkHost net 31 tc
  let (b, _) ← mkHost net 32 tc
  let quicA ← listenOn a "/ip4/127.0.0.1/udp/4101/quic-v1"
  let tcpA ← listenOn a "/memory/201"
  match ← b.dial (← withPeer quicA a.localPeer) with
  | .ok p => r.check "host secured: a dial over the secured path proves the peer" (p == a.localPeer)
  | .error e => r.check s!"host secured: a dial over the secured path succeeds ({e})" false
  r.check "host secured: the dialer's stream echoes" (← echoOnce b a.localPeer "secured")
  r.check "host secured: the listener's stream echoes" (← echoOnce a b.localPeer "back")
  -- The ranker: TCP first in the peerstore, QUIC first in the dial.
  let (c, _) ← mkHost net 33 tc
  c.addAddrs a.localPeer [tcpA, quicA]
  r.check "host secured: dialPeer reaches the peer" ((← c.dialPeer a.localPeer) matches .ok _)
  -- A serves a stream of C's only once it has registered C's session, so
  -- after this echo A's stream to C takes that session, and dials nothing.
  r.check "host secured: the ranked dial's session serves a stream" (← echoOnce c a.localPeer "warm")
  let seen : Chan StreamContext ← Chan.new 1
  c.setHandler { id := ctxId, handle := fun ctx s => do discard <| seen.send ctx; s.close }
  let opened ← a.newStream c.localPeer [ctxId]
  r.check "host secured: the listener opens a stream back" (opened matches .ok _)
  -- Park: the handler's send wakes it; a stream that failed to open
  -- sends nothing, so the receive waits only when the open passed.
  if opened matches .ok _ then
    match ← seen.recv with
    | some ctx =>
      r.check "host secured: the ranker dials the QUIC address first" (ctx.remoteAddr == quicA)
    | none => r.check "host secured: the dialer's handler saw a context" false
  -- One peer over both paths at once.
  let (e, _) ← mkHost net 34 tc
  let viaTcp ← (Conc.Wrap.spawn (e.dial tcpA) :
    BaseIO (Task (Except IO.Error (Except Libp2p.Host.Error PeerId))))
  let viaQuic ← (Conc.Wrap.spawn (e.dial quicA) :
    BaseIO (Task (Except IO.Error (Except Libp2p.Host.Error PeerId))))
  let both := (← Conc.Wrap.await viaTcp, ← Conc.Wrap.await viaQuic)
  r.check "host secured: dials over both paths both reach the peer"
    (both matches (.ok (.ok _), .ok (.ok _)))
  r.check "host secured: the peer stays served after the dedup" (← echoOnce e a.localPeer "one")
  e.close
  c.close
  b.close
  a.close
  tc.close

/-- The policy on the secured paths. A gater that refuses the inbound
connection refuses it before its upgrade, so its scope never opens. A
gater that refuses the proved peer refuses after the handshake, and the
host releases the scope. By the end, the hosts have released every
scope they opened. -/
private def securedPolicyChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let opened ← OnceRef.new (0 : Nat)
  let released ← OnceRef.new (0 : Nat)
  let (dialer, _) ← mkHost net 41 tc
  let (shut, failsShut) ← mkHost net 42 tc (gater := Policy.denyingGater)
    (resources := countingResources opened released)
  let addrShut ← listenOn shut "/ip4/127.0.0.1/udp/4201/quic-v1"
  let refused ← try pure ((← dialer.dial addrShut) matches .error _) catch _ => pure true
  r.check "host secured: a denying gater refuses an inbound connection" refused
  r.check "host secured: the refusal opens no scope" ((← (opened.get : BaseIO Nat)) == 0)
  r.check "host secured: the refusal is no failure" (← (failsShut.tryRecv : BaseIO _)).isNone
  let (picky, failsPicky) ← mkHost net 43 tc (gater := securedOnlyGater)
    (resources := countingResources opened released)
  let addrPicky ← listenOn picky "/ip4/127.0.0.1/udp/4202/quic-v1"
  -- A secured transport finishes the whole handshake, the muxer's
  -- included, before the listener's checkpoint runs. So the dialer may
  -- hold a session when the refusal comes, and the refusal then closes
  -- it. go-libp2p's QUIC listener closes a connection its gater refuses
  -- the same way (`InterceptSecured`, then `CloseWithError`). Real time:
  -- the close has 5 s to reach the dialer.
  discard <| try (some <$> dialer.dial addrPicky) catch _ => pure none
  let mut gone := false
  for _ in List.range 250 do
    if !(← (dialer.connected picky.localPeer : BaseIO Bool)) then
      gone := true
      break
    select #[← Park.sleep 20 ()]
  r.check "host secured: the secured checkpoint refuses an inbound peer, and the dialer's session ends"
    gone
  r.check "host secured: the inbound secured refusal leaves no session"
    !(← (picky.connected dialer.localPeer : BaseIO Bool))
  r.check "host secured: the secured refusal is no failure"
    (← (failsPicky.tryRecv : BaseIO _)).isNone
  -- The outbound checkpoint: the proved peer is refused before the
  -- session is served.
  let (open_, _) ← mkHost net 44 tc
  let addrOpen ← listenOn open_ "/ip4/127.0.0.1/udp/4203/quic-v1"
  r.check "host secured: the secured checkpoint refuses an outbound peer"
    ((← picky.dial addrOpen) matches .error (.gated .secured))
  picky.close
  shut.close
  open_.close
  dialer.close
  r.check "host secured: every scope opened is released"
    ((← (opened.get : BaseIO Nat)) == (← (released.get : BaseIO Nat)))
  tc.close

/-- The close reaches the secured paths in their handshakes (root
§5.5), with no time passing on the test clock. A raw connection to a
secured listener sends nothing, so the listener's accept parks in its
upgrade; the host's close ends that upgrade. A secured dial to a raw
listener that answers nothing parks in its upgrade; the dialer's close
ends that dial with `closing`. -/
private def securedShutdownChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let tc ← TestClock.new
  let (a, _) ← mkHost net 51 tc
  let addrA ← listenOn a "/ip4/127.0.0.1/udp/4301/quic-v1"
  let some raw ← net.transport.dial addrA | throw <| IO.userError "raw dial failed"
  a.close
  r.check "host secured: close reaches an accept in its upgrade, and returns" (← endsSoon raw)
  let (b, _) ← mkHost net 52 tc
  let silent ← net.transport.listen (← ma "/ip4/127.0.0.1/udp/4302/quic-v1")
  let pending ← (Conc.Wrap.spawn (b.dial silent.addr) :
    BaseIO (Task (Except IO.Error (Except Libp2p.Host.Error PeerId))))
  -- The silent listener takes the connection, and answers nothing.
  let some held ← silent.accept | throw <| IO.userError "raw accept failed"
  b.close
  r.check "host secured: close ends a secured dial in its upgrade with closing"
    ((← Conc.Wrap.await pending) matches .ok (.error .closing))
  held.closeQuietly
  silent.close
  tc.close

end Swarm

def Host.run (r : Runner) : IO Unit := do
  r.section "host" "(packages/libp2p/host/docs/PLAN.md, test milestones, units 1a and 1b)"
  dedupChecks r
  (concurrentDedupChecks r).run
  (livenessChecks r).run
  (handlerChecks r).run
  (peerstoreChecks r).run
  errorChecks r
  for (label, act) in [("pipeline", pipelineChecks r), ("answers", answerChecks r),
      ("policy", policyChecks r), ("silent peer", silentPeerChecks r),
      ("shutdown", shutdownChecks r), ("hand-over", handOverChecks r),
      ("mplex", mplexChecks r), ("secured", securedChecks r),
      ("secured policy", securedPolicyChecks r),
      ("secured shutdown", securedShutdownChecks r)] do
    try act.run
    catch e => r.check s!"host {label}: runs ({e})" false

end Tests