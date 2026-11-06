import Std.Data.HashMap
import Tests.Support
import Streams
import Libp2p.Identity
import Libp2p.Core

/-!
# Core suite (unit W5.2)

The checks of `packages/libp2p/core/docs/PLAN.md`, "Test milestones
(unit 1)". The package holds types only, so most milestones close at
compile time: each seam takes a test value, and an `example` or a
definition the build type-checks shows it. The runtime checks run the
doubles over the sim transport of `net/streams`, render each
`Core.Error` arm, and look a handler up by `ProtocolId`.

The doubles live here. The production values and their own test values
belong to the implementation packages (the core pair, "Test values").
-/

set_option autoImplicit false

namespace Tests

open Conc Streams Multiformats Libp2p.Identity Libp2p.Core

/-- The bytes of a string. -/
private def b (s : String) : ByteArray := s.toUTF8

/-- A multiaddr from its text form. -/
private def ma (s : String) : Async Multiaddr := do
  match Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- A peer id for the doubles: the inlined id of an empty key. The size
bound `0 ≤ 42` holds by evaluation. -/
private def testPeer : PeerId := PeerId.inline .empty (by decide)

/-! ## The doubles -/

/-- A security protocol that authenticates nothing: the secure surface
is the connection itself, and both peer ids are `peer`. It refuses a
negotiation leftover, so the error path of the seam has a test too. -/
private def plaintext (peer : PeerId) : SecurityProtocol where
  id := ⟨"/test/plaintext"⟩
  handshake := fun _ c leftover => do
    unless leftover.isEmpty do
      throw (.protocol "the plaintext double takes no leftover")
    return { toConnection := c, localPeer := peer, remotePeer := peer,
             leftover := .empty, join := pure () }

/-- A muxer whose session serves no stream: an open fails with
`closed`, and an accept answers `none`, as after a close. -/
private def emptyMuxer : Muxer where
  id := ⟨"/test/empty-mux"⟩
  «open» := fun _ _ _ => return {
    openStream := fun _ => throw (.closed "the empty session opens no stream")
    accept := pure none
    close := pure ()
    join := pure () }

/-- A handler that half-closes the stream it gets. -/
private def closer (id : ProtocolId) : StreamHandler where
  id := id
  -- `s.close` runs in `Async`; `ExceptT` lifts it with no error.
  handle := fun s => s.close

/-! ## Compile milestones -/

-- `Role` derives `DecidableEq`, so `decide` separates the two arms.
example : Role.initiator ≠ Role.responder := by decide

-- `Repr` and `Hashable` exist on `Role`; instance search finds both.
example : Repr Role := inferInstance
example : Hashable Role := inferInstance

-- The standard classes of §3.2 on `ProtocolId`.
example : DecidableEq ProtocolId := inferInstance
example : Hashable ProtocolId := inferInstance
example : Ord ProtocolId := inferInstance
example : ToString ProtocolId := inferInstance

-- A `SecureConn` runs a muxer through its parent projection, the path
-- the upgrader takes from the handshake to the muxer stage.
example (m : Muxer) (r : Role) (sc : SecureConn) : ExceptT Libp2p.Core.Error Async MuxSession :=
  m.open r sc.toConnection .empty

-- The policy seams admit their doubles: a permissive gater, a manager
-- that admits everything and counts nothing, and a ranker that keeps
-- the order and adds no delay.
example : ConnectionGater :=
  { allowDial := fun _ _ => pure true, allowInbound := fun _ _ => pure true,
    allowSecured := fun _ _ _ _ => pure true }
example : ResourceManager :=
  let free : Reservation := { release := pure () }
  { openConnection := fun _ _ _ => pure (some {
      setPeer := fun _ => pure true
      reserveStream := pure (some free)
      reserveMemory := fun _ => pure (some free)
      release := pure () }) }
example : AddressRanker := { rank := List.map fun a => { addr := a, delayMs := 0 } }

/-! ## Runtime checks -/

/-- The doubles over a sim pair: handshake, the secure surface, the
muxer stage, and the error path. -/
private def seamChecks (r : Runner) : Async Unit := do
  let net ← Sim.Net.new
  let l ← net.transport.listen (← ma "/ip4/127.0.0.1/tcp/4101")
  let some client ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
  let some server ← l.accept | throw <| IO.userError "accept failed"
  -- The owner closes the listener, then joins it (§4.1, rule 2).
  l.close
  l.join

  -- The handshake answers a `SecureConn` whose surface reaches the peer.
  match ← (plaintext testPeer).handshake .initiator client .empty with
  | .error e =>
    r.check s!"the plaintext handshake succeeds ({e})" false
    client.close
  | .ok sc =>
    r.check "the handshake records the remote peer id" (sc.remotePeer == testPeer)
    r.check "the secure connection keeps the addresses" (sc.remoteAddr == client.remoteAddr)
    sc.write (b "hi")
    let got ← server.readExactly 2
    r.check "the secure write reaches the peer"
      (got.any fun (x, rest) => x.toList == (b "hi").toList && rest.isEmpty)
    -- The muxer stage runs over the parent projection. Its leftover is
    -- what the muxer negotiation over-read, and this test runs no
    -- negotiation, so it is empty. `sc.leftover` never goes here.
    match ← emptyMuxer.open .initiator sc.toConnection .empty with
    | .error e => r.check s!"the muxer opens a session ({e})" false
    | .ok session =>
      r.check "an ended session accepts nothing" ((← session.accept).isNone)
      r.check "an ended session refuses a stream"
        (match ← session.openStream ⟨"/test/x"⟩ with | .error (.closed _) => true | _ => false)
      session.close
      r.check "the session joins clean" ((← session.join) matches .ok ())
    sc.close
    r.check "the secure connection joins clean" ((← sc.join) matches .ok ())

  -- The seam reports the implementation's failure as a `Core.Error` arm.
  let refused ← (plaintext testPeer).handshake .responder server (b "x")
  r.check "a seam failure arrives as Core.Error.protocol"
    (match refused with | .error (.protocol _) => true | _ => false)
  server.close

/-- The `Core.Error` arms construct, and each renders its kind and its
detail for the log. -/
private def errorChecks (r : Runner) : IO Unit := do
  let arms : List (Libp2p.Core.Error × String) :=
    [(.protocol "bad frame", "protocol error: bad frame"),
     (.authentication "bad signature", "authentication failure: bad signature"),
     (.timeout "30000 ms", "timeout: 30000 ms"),
     (.closed "session ended", "closed: session ended")]
  for (e, line) in arms do
    r.check s!"Core.Error renders {repr e}" (toString e == line)

/-- A registry keyed by `ProtocolId`, the shape §3.10 gives the host. -/
private def registryChecks (r : Runner) : IO Unit := do
  let ping : ProtocolId := ⟨"/ipfs/ping/1.0.0"⟩
  let ident : ProtocolId := ⟨"/ipfs/id/1.0.0"⟩
  let registry : Std.HashMap ProtocolId StreamHandler :=
    [closer ping, closer ident].foldl (fun m h => m.insert h.id h) {}
  r.check "the registry finds a handler by its id"
    ((registry.get? ⟨"/ipfs/ping/1.0.0"⟩).any (·.id == ping))
  r.check "the registry misses an unknown id" (registry.get? ⟨"/ipfs/ping/2.0.0"⟩).isNone
  r.check "a protocol id prints its wire text" (toString ping == "/ipfs/ping/1.0.0")
  r.check "protocol ids order by their text" (compare ident ping == .lt)

def Core.run (r : Runner) : IO Unit := do
  r.section "core" "(packages/libp2p/core/docs/PLAN.md, test milestones, unit 1)"
  (seamChecks r).run
  errorChecks r
  registryChecks r

end Tests
