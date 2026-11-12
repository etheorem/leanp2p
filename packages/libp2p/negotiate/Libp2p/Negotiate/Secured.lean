import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Negotiate.Upgrade

/-!
# A secured transport over an upgrade

`securedOver` fills the `SecuredTransport` seam of `libp2p/core` with
any `Streams.Transport` and the upgrade of this package. Its dial and
its accept run the security stage and the muxer stage themselves. Each
answers a `SecuredSession`, as a QUIC connection arrives. go-libp2p's
TCP transport has the same shape: it runs the upgrader inside its own
dial (`vendor/go-libp2p/p2p/transport/tcp/tcp.go`, line 302).

Over the in-memory sim transport (`Streams.Sim`), with a fixed-key
security protocol and a muxer, it is the sim value of the seam. The
host suite runs its secured paths on it with no socket (PRINCIPLES 1.4;
root ARCHITECTURE §3.1).

## The admission and the accept

The listener admits each accepted connection through the owner's
`Admit` before the first byte of its upgrade, as the host admits a TCP
connection. A refused connection closes at once. An admitted one
upgrades inside `accept`, one at a time, under the unauthenticated
deadline of the upgrade (root §5.4). A failure releases its scope, and
`accept` takes the next connection.

## The parks and their closes

A dial parks on its upgrade and on its `abort`. The close of `abort`
closes the connection, which ends the upgrade (PRINCIPLES 3.1), and the
dial answers `closed`. An accept parks on the listener, then on the
upgrade of the connection it took. The listener's `close` closes the
listener and that connection, so a closing host waits for no upgrade
(root §5.5).
-/

set_option autoImplicit false

namespace Libp2p.Negotiate

open Conc Streams Multiformats Libp2p.Identity Libp2p.Core

/-- The secured session of an upgraded connection. -/
private def sessionOf (conn : Connection) (localPeer : PeerId) (s : MuxSession)
    (remotePeer : PeerId) : SecuredSession :=
  { session := s, localPeer, remotePeer
    localAddr := conn.localAddr, remoteAddr := conn.remoteAddr }

/-- The upgrade as a value: a fault of the work becomes `closed`, so the
task that runs it always answers. -/
private def upgradeAnswer (clock : Clock) (role : Role) (conn : Connection)
    (expected : Option PeerId) (secs : List SecurityProtocol) (muxers : List Muxer) :
    Async (Except Core.Error (MuxSession × PeerId)) := do
  try (upgradeWith clock role conn .empty expected secs muxers).run
  catch e => return .error (.closed s!"upgrade: {e}")

/-- Dial `addr` through `t` and upgrade the connection, ending it at the
close of `abort` (the module doc, "The parks and their closes"). -/
private def dialUpgraded (t : Streams.Transport) (localPeer : PeerId)
    (secs : List SecurityProtocol) (muxers : List Muxer) (clock : Clock) (addr : Multiaddr)
    (expected : Option PeerId) (abort : Chan Unit) : Async (Except Core.Error SecuredSession) := do
  let some conn ← t.dial addr | return .error (.closed s!"nothing listens at {addr.describe}")
  let done : Chan (Except Core.Error (MuxSession × PeerId)) ← Chan.new 1
  let tasks ← TaskSet.new
  tasks.spawn do discard <| done.send (← upgradeAnswer clock .initiator conn expected secs muxers)
  -- Park: the upgrade's end wakes it, and so does the close of `abort`.
  let first ← select #[Park.recv done Sum.inl, Park.recv abort fun _ => Sum.inr ()]
  let answer ← match first with
    | .inl (some r) => pure r
    | .inl none => pure (.error (.closed "the upgrade ended with no answer"))
    | .inr () => do
      -- The close ends the upgrade, which answers `done`.
      conn.closeQuietly
      match ← done.recv with
      | some (.ok (s, _)) =>
        -- The upgrade finished as the abort came: the session is ours
        -- to end.
        discard s.close.toBaseIO
        discard s.join.run
      | _ => pure ()
      pure (.error (.closed "the dialer has stopped"))
  tasks.joinAll
  return answer.map fun (s, peer) => sessionOf conn localPeer s peer

/-- The state of a listener's accept: the connection whose upgrade runs
now, and whether `close` came. -/
private structure AcceptState where
  inFlight : Option Connection := none
  closed : Bool := false

/-- The next connection of `l` that the owner admits and the upgrade
proves, with its scope (the module doc, "The admission and the
accept"). The function is `partial`: it ends when one passes or the
listener closes, and no measure bounds the failed peers before that. -/
private partial def acceptUpgraded (l : Streams.Listener) (admit : Admit) (localPeer : PeerId)
    (secs : List SecurityProtocol) (muxers : List Muxer) (clock : Clock)
    (state : OnceRef AcceptState) : Async (Option (SecuredSession × ConnectionScope)) := do
  -- Park: a dialed connection wakes it, and so does the close.
  let some conn ← l.accept | return none
  let some scope ← (admit conn.localAddr conn.remoteAddr : BaseIO (Option ConnectionScope))
    | conn.closeQuietly
      acceptUpgraded l admit localPeer secs muxers clock state
  -- Register the upgrade, unless `close` came first: one atomic step, so
  -- `close` either finds the connection or the flag stops it here.
  let started ← (state.updateGet fun s =>
    if s.closed then (false, s) else (true, { s with inFlight := some conn }) : BaseIO Bool)
  if !started then
    conn.closeQuietly
    scope.release
    return none
  -- Park: the upgrade reads the connection, and `close` closes it.
  let r ← upgradeAnswer clock .responder conn none secs muxers
  state.update fun s => { s with inFlight := none }
  match r with
  -- The owner names the proved peer on the scope (`ConnectionScope.setPeer`).
  | .ok (s, peer) => return some (sessionOf conn localPeer s peer, scope)
  | .error _ =>
    scope.release
    acceptUpgraded l admit localPeer secs muxers clock state

/-- The secured transport of `t` and the upgrade (the module doc). The
dial and the accept run the security protocols `secs` and the muxers
`muxers` in preference order, on `clock`. `localPeer` names the
identity the security protocols prove. `handles` decides the addresses
the value takes, so a host can hold it beside a `Streams.Transport` of
the same addresses. -/
def securedOver (t : Streams.Transport) (handles : Multiaddr → Bool) (localPeer : PeerId)
    (secs : List SecurityProtocol) (muxers : List Muxer) (clock : Clock := Clock.system) :
    SecuredTransport where
  handles
  dial := fun addr expected abort =>
    ExceptT.mk (dialUpgraded t localPeer secs muxers clock addr expected abort)
  listen := fun addr admit => do
    let l ← t.listen addr
    let state ← OnceRef.new ({} : AcceptState)
    return {
      addr := l.addr
      accept := acceptUpgraded l admit localPeer secs muxers clock state
      close := do
        let inFlight ← (state.updateGet fun s => (s.inFlight, { s with closed := true }) :
          BaseIO (Option Connection))
        l.close
        if let some c := inFlight then c.closeQuietly
      join := l.join }

end Libp2p.Negotiate
