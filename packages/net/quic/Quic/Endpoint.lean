import Std.Data.HashMap
import Std.Async.UDP
import Conc
import Streams
import Tls
import QuicNative
import Quic.Constants
import Quic.Error
import Quic.Address
import Quic.View
import Quic.Loop

/-!
# Dial and listen

`Quic.dial` and `Quic.listen` open an endpoint on a bound UDP socket,
with the numbers of `Quic/Constants.lean`, and start its three tasks:
the loop, the reader, and the ticker (`Quic/Loop.lean`). The endpoint's
task set owns them (PRINCIPLES 3.2).

A dial has its own endpoint, and its connection owns it: the
connection's `join` ends the endpoint too. A listener's endpoint holds
every connection that peers dial to its address. The listener's `join`
ends once the listener is closed and its last connection has ended.

## The certificate check

The handshake runs the caller's check inside libssl's verify callback,
as `net/tls` does over TCP (`QuicNative`, "The certificate check"). A
dial takes one check. A listener takes an admission (`Admitted`), which
gives each new connection its own check when the connection's first
datagram arrives.
-/

set_option autoImplicit false

namespace Quic

open Conc Streams Multiformats

/-- The unspecified address of a family, port 0: the bind of a dialing
endpoint. -/
private def anyOf : Std.Net.SocketAddress → Std.Net.SocketAddress
  | .v4 _ => .v4 ⟨Std.Net.IPv4Addr.ofParts 0 0 0 0, 0⟩
  | .v6 _ => .v6 ⟨Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 0, 0⟩

/-- The bounds of a listener's new connections (`QuicNative`, "The
bounds of new connections"). The defaults are the numbers of
`Quic/Constants.lean`, and every caller but a suite keeps them; a suite
passes smaller ones to reach a bound with a few datagrams. -/
structure Bounds where
  /-- The server connections in their handshake at once. -/
  maxHandshakes : Nat := Quic.maxHandshakes
  /-- The count past which a new client proves its address first. -/
  retryThreshold : Nat := Quic.retryThreshold
  /-- The closing periods the listener keeps at once. -/
  maxClosingPeriods : Nat := Quic.maxClosingPeriods

/-- An endpoint over a bound socket, with the numbers of
`Quic/Constants.lean` and the bounds `bounds`. -/
private def open_ {α : Type} (ctx : Tls.Context) (socket : Std.Async.UDP.Socket) (accept : Bool)
    (admit : (localAddr remoteAddr : Multiaddr) → BaseIO (Option (Admitted α))) (clock : Clock)
    (bounds : Bounds) : IO (Except Error (Shared α)) := do
  let local_ ← socket.getSockName
  let some native ← QuicNative.endpointNew ctx.native (toShim local_) accept
      maxStreamsBidi.toUInt64 streamWindow.toUInt64 streamWindowMax.toUInt64
      connWindow.toUInt64 connWindowMax.toUInt64 idleTimeoutMs.toUInt64 keepAliveMs.toUInt64
      handshakeTimeoutMs.toUInt64 bounds.maxHandshakes.toUInt64 bounds.retryThreshold.toUInt64
      bounds.maxClosingPeriods.toUInt64 connectionRefused invalidToken
    | return .error .endpoint
  let some localAddr := multiaddrOf local_ | return .error .address
  let listener ← if accept then some <$> Chan.new listenBacklog else pure none
  return .ok {
    native, socket, clock, localAddr, admit
    selfAddr := selfAddress local_
    datagrams := ← Chan.new datagramQueueCap
    commands := ← Chan.newUnbounded
    stopAccepting := ← Chan.new 1
    reading := ← OnceRef.new {}
    listener
    alarm := ← Alarm.new
    ticks := ← Chan.new 1
    tasks := ← TaskSet.new }

/-- Start the three tasks of an endpoint. -/
private def start {α : Type} (sh : Shared α) (st : LoopState α) : BaseIO Unit := do
  sh.tasks.spawn (loop sh st)
  sh.tasks.spawn (reader sh)
  sh.tasks.spawn (ticker sh)

/-- Dial the `quic-v1` address `remote` on the TLS context `ctx`, with
the certificate check `check`. The answer is the connection once the
handshake has finished. The dial has its own UDP socket, bound to a port
the system picks, and the connection's join ends the endpoint. The
handshake's deadline is the unauthenticated deadline of root §5.4,
inside the shim (`handshakeTimeoutMs`).

`abort`, when given, ends a dial still in its handshake: its close
closes the connection, and the dial answers `.ended`, as a host's
shutdown closes its pending connections (root §5.5). A dial whose
handshake ends as the abort closes still answers `.ended`, and closes
the connection it got. -/
def dial (ctx : Tls.Context) (remote : Multiaddr) (check : Check) (clock : Clock := Clock.system)
    (abort : Option (Chan Unit) := none) : Async (Except Error Conn) := do
  let some ra := socketAddress? remote | return .error .address
  let socket ← Std.Async.UDP.Socket.mk
  -- The shim's bind, with no address reuse: a port of its own, which no
  -- other dial shares (`QuicNative.udpBind`).
  QuicNative.udpBind socket.native (toShim (anyOf ra))
  -- A dialing endpoint takes no new connection, so its admission never
  -- runs.
  match ← open_ (α := Unit) ctx socket false (fun _ _ => pure none) clock {} with
  | .error e => return .error e
  | .ok sh =>
    let handle ← QuicNative.connect sh.native (toShim ra) (← sh.clock.nowMs).toUInt64 check
    if handle == 0 then return .error .address
    let ready : Chan (Except Error Conn) ← Chan.new 1
    -- The ascription names the value type: the update reads no field that
    -- fixes it.
    let fresh ← (newConn : BaseIO (ConnState Unit))
    let c := { fresh with ready := some ready }
    start sh { conns := ({} : Std.HashMap UInt64 (ConnState Unit)).insert handle c,
               accepting := false }
    -- Park: the handshake's end wakes it, and so does the close of
    -- `abort`. The end of the connection also answers the slot.
    let first ← match abort with
      | none => Sum.inl <$> ready.recv
      | some a => select #[Park.recv ready Sum.inl, Park.recv a fun _ => Sum.inr ()]
    let (aborted, answer) ← match first with
      | .inl r => pure (false, r)
      | .inr () => do
        discard <| (sh.commands.trySend (.close handle orderlyClose "the dialer has stopped") :
          BaseIO Bool)
        -- Park: the close ends the connection, which answers the slot.
        pure (true, ← ready.recv)
    match answer with
    | some (.ok conn) =>
      if !aborted then return .ok conn
      discard conn.join
      return .error .ended
    | some (.error e) =>
      sh.tasks.joinAll
      return .error (if aborted then .ended else e)
    | none =>
      sh.tasks.joinAll
      return .error endedError

/-- A source of the QUIC connections that peers dial to one address,
each with the value its admission gave (`Admitted`). -/
structure Listener (α : Type) where
  /-- The address the listener serves, with the port the system picked
  for a port of 0. -/
  addr : Multiaddr
  /-- The next connection, once its handshake has finished. After
  `close`, the connections still in the queue, then `none`: quic-go's
  `Accept` drains its queue the same way (`server.go`, `accept`). The
  caller owns each connection it takes, and its value, and must close
  the connection. -/
  accept : Async (Option (Conn × α))
  /-- Stop taking connections. The connections the listener gave stay
  open until their owners close them, and so do those still in the
  queue, which `accept` still gives. A second close does nothing. -/
  close : BaseIO Unit
  /-- Wait until the endpoint has ended: the listener is closed, and its
  last connection has ended. -/
  join : Async Unit

/-- The fault of a listen that cannot start: an address that is no
`quic-v1` multiaddr, or an endpoint the shim refused. A listen fails
through faults, as the TCP transport's does (`Streams.Tcp`). -/
private def listenFault (what : String) : IO.Error :=
  .invalidArgument none 0 s!"quic: {what}"

/-- Listen on the `quic-v1` address `addr` with the TLS context `ctx`.
`admit` decides each new connection by our address and the peer's when
its first datagram arrives, and gives its certificate check
(`Admitted`). `bounds` holds the bounds of new connections. An address
in use is a fault. -/
def listen {α : Type} (ctx : Tls.Context) (addr : Multiaddr)
    (admit : (localAddr remoteAddr : Multiaddr) → BaseIO (Option (Admitted α)))
    (clock : Clock := Clock.system) (bounds : Bounds := {}) : Async (Listener α) := do
  let some sa := socketAddress? addr
    | throw <| listenFault s!"{addr.describe} is not /ip4|ip6/<addr>/udp/<port>/quic-v1"
  let socket ← Std.Async.UDP.Socket.mk
  -- The shim's bind, with no address reuse (`QuicNative.udpBind`).
  QuicNative.udpBind socket.native (toShim sa)
  match ← open_ ctx socket true admit clock bounds with
  | .error e => throw <| listenFault (toString e)
  | .ok sh =>
    let some accepts := sh.listener | throw <| listenFault "the endpoint has no accept queue"
    start sh { accepting := true }
    return {
      addr := sh.localAddr
      -- Park: a connection's handshake wakes it, and so does `close`.
      accept := accepts.recv
      close := sh.stopAccepting.close
      join := sh.tasks.joinAll }

/-- The admission that takes every connection with the check `check`
and no value of its own. -/
def admitAll (check : Check) : Multiaddr → Multiaddr → BaseIO (Option (Admitted Unit)) :=
  fun _ _ => pure (some { check, value := (), release := pure () })

end Quic
