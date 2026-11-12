import Tests.Support
import Std.Async.UDP
import Crypto
import Streams
import Tls
import TlsNative
import Quic
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Security
import Libp2p.Quic
import Libp2p.Host
import Libp2p.Protocols

/-!
# The QUIC suite (unit W4.4)

The checks of `packages/net/quic/docs/PLAN.md` and
`packages/libp2p/quic/docs/PLAN.md`, "Test milestones". They run
endpoints over loopback UDP, since QUIC's transport is the UDP socket
itself, as the TCP suite runs over loopback TCP (root ARCHITECTURE §6:
only the transport suites leave the sim). The `net/quic` checks give the
engine a check that takes any certificate; the libp2p checks give it
the libp2p TLS checks.

* the handshake in one pair, the ALPN, and both peer certificates;
* a stream echo, small and past the send cap and the windows;
* the half-close: our FIN, then the peer's reply;
* many streams at once;
* the reset: ours drops the bytes that wait, and the peer's ends our
  reads and our writes;
* the close of a connection by either side, and both joins;
* the same echo over IPv6 loopback;
* a listener that closes, then ends with its last connection;
* an ended endpoint releases its UDP socket;
* a full accept queue, which refuses with CONNECTION_REFUSED;
* the handshake deadline, on the test clock;
* a client with another ALPN name, and a chain of two certificates;
* the libp2p value: the peer ids, an unexpected peer and an expired
  certificate refused inside the handshake, a certificate without the
  extension, a listener whose wall clock fails, the fixed-key value;
* the QUIC-first ranker, and two hosts over QUIC with a ping.
-/

set_option autoImplicit false

namespace Tests.QuicSuite

open Conc Streams

/-- An address, or a failed run. -/
private def ma (s : String) : Async Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- The value of an `Except`, or a failed run. -/
private def expectOk {ε α : Type} [ToString ε] (where_ : String) : Except ε α → Async α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{where_}: {e}"

/-- The check of an engine test: it takes any certificate. -/
private def acceptAny : Quic.Check := fun _ => none

/-- A TLS context with a fresh certificate and the ALPN `alpn`. The
engine checks no certificate of its own (`acceptAny`), so the
extension is arbitrary. -/
private def context (alpn : String := "quic-test") : Async Tls.Context := do
  let key ← match ← Crypto.p256Generate.run with
    | .ok k => pure k
    | .error _ => throw <| IO.userError "p256 key"
  let wall := 1800000000
  let cert ← match ← (Crypto.issue key "1.3.6.1.4.1.53594.1.1" ⟨#[0x30, 0x00]⟩ false
      (wall - 3600 * 24 * 365 * 10) (wall + 3600 * 24 * 365 * 10)).run with
    | .ok c => pure c
    | .error _ => throw <| IO.userError "issue"
  expectOk "context" (← Tls.Context.new cert key alpn)

/-- Read a stream to its end. -/
private def readAll (s : Stream) : Async (ByteArray × Option Streams.Error) := do
  let mut acc := ByteArray.empty
  repeat
    match ← s.read with
    | .ok (some b) => acc := acc ++ b
    | .ok none => return (acc, none)
    | .error e => return (acc, some e)
  return (acc, none)

/-- A listener of the engine suite: its admission takes every
connection, with no value of its own. -/
private abbrev Listener := Quic.Listener Unit

/-- A listener with the engine check that takes any certificate. -/
private def listenAny (ctx : Tls.Context) (addr : String := "/ip4/127.0.0.1/udp/0/quic-v1")
    (clock : Clock := Clock.system) (bounds : Quic.Bounds := {}) : Async Listener := do
  Quic.listen ctx (← ma addr) (Quic.admitAll acceptAny) clock bounds

/-- The next connection of an engine listener. -/
private def acceptConn (l : Listener) : Async (Option Quic.Conn) :=
  (·.map Prod.fst) <$> l.accept

/-- A connected pair: the dialer's connection and the listener's. -/
private def pair (l : Listener) (ctx : Tls.Context) : Async (Quic.Conn × Quic.Conn) := do
  let t ← (Conc.Wrap.spawn (acceptConn l) : BaseIO (Task (Except IO.Error (Option Quic.Conn))))
  let d ← expectOk "dial" (← Quic.dial ctx l.addr acceptAny)
  match ← Conc.Wrap.await t with
  | .ok (some a) => return (d, a)
  | _ => throw <| IO.userError "accept"

/-- The bytes of a pattern. -/
private def pattern (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun k => UInt8.ofNat ((k * 7 + 3) % 251)⟩

/-- Echo every stream of `c` until its end: read the stream to its
FIN, write the bytes back, and close. The function is `partial`: it
ends when the connection's accept answers `none`. -/
private partial def echoAll (c : Quic.Conn) : Async Unit := do
  let streams ← TaskSet.new
  repeat
    let some s ← c.accept | break
    streams.spawn do
      let (b, _) ← readAll s
      discard <| s.write b
      s.close
  streams.joinAll

/-- Close both connections in order, and join them. -/
private def closeBoth (d a : Quic.Conn) : Async Unit := do
  d.close Quic.orderlyClose "done"
  discard d.join
  discard a.join

/-! ## The addresses -/

/-- The edge of the address codec: a socket address goes to the shim's
bytes and back, and the bytes follow the proved layout
(`Quic.ShimAddr.decode_encode`). The samples cover both families and
both ends of the port range. -/
private def addressChecks (r : Runner) : IO Unit := do
  let samples : List Std.Net.SocketAddress := [
    .v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 4001⟩,
    .v4 ⟨Std.Net.IPv4Addr.ofParts 0 0 0 0, 0⟩,
    .v4 ⟨Std.Net.IPv4Addr.ofParts 255 255 255 255, 65535⟩,
    .v6 ⟨Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 1, 443⟩,
    .v6 ⟨Std.Net.IPv6Addr.ofParts 0x2001 0xdb8 0x3333 0x4444 0x5555 0x6666 0x7777 0x8888, 65535⟩]
  for sa in samples do
    let bytes := Quic.toShim sa
    r.check s!"quic address: {bytes.size} shim bytes read back"
      ((Quic.ofShim? bytes).map Quic.toShim == some bytes)
    r.check s!"quic address: the {bytes.size} bytes follow the proved layout"
      (Quic.ShimAddr.decode? (bytes.toList.map (·.toNat)) == some (Quic.shimOf sa))
  r.check "quic address: a length that names no family reads as none"
    (Quic.ofShim? ⟨#[4, 127, 0, 0, 1]⟩).isNone
  -- The reason text of an end event: the peer's bytes never panic.
  r.check "quic reason: valid text stays whole" (Quic.reasonText "done".toUTF8 == "done")
  -- "é" is 0xC3 0xA9; a cut after its first byte leaves the text before.
  r.check "quic reason: a character split by the cut drops its bytes"
    (Quic.reasonText ⟨#[0x61, 0x62, 0xC3]⟩ == "ab")
  r.check "quic reason: bytes that are no UTF-8 become a placeholder"
    ((Quic.reasonText ⟨#[0xFF, 0xFE, 0xFD, 0xFC, 0xFB]⟩).startsWith "(a reason of 5 bytes")
  r.check "quic reason: a short reason that is no UTF-8 becomes a placeholder, never empty"
    ((Quic.reasonText ⟨#[0xFF]⟩).startsWith "(a reason of 1 bytes")
  -- The socket's own address: an unspecified IP becomes the loopback of
  -- its family, with the port kept; any other address stays.
  -- TODO(lean v4.36): remove these three with `Quic.selfAddress`.
  r.check "quic address: 0.0.0.0 receives its own datagram at 127.0.0.1"
    (Quic.selfAddress (.v4 ⟨Std.Net.IPv4Addr.ofParts 0 0 0 0, 4001⟩)
      == .v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 4001⟩)
  r.check "quic address: :: receives its own datagram at ::1"
    (Quic.selfAddress (.v6 ⟨Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 0, 4001⟩)
      == .v6 ⟨Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 1, 4001⟩)
  r.check "quic address: a bound IP receives its own datagram there"
    (Quic.selfAddress (.v4 ⟨Std.Net.IPv4Addr.ofParts 10 0 0 7, 4001⟩)
      == .v4 ⟨Std.Net.IPv4Addr.ofParts 10 0 0 7, 4001⟩)
  -- The multiaddr forms: `quic-v1` is handled, the draft `/quic` is not.
  match Multiformats.Multiaddr.parse? "/ip4/127.0.0.1/udp/1234/quic-v1",
      Multiformats.Multiaddr.parse? "/ip4/12.34.56.78/udp/4321/quic",
      Multiformats.Multiaddr.parse? "/ip4/127.0.0.1/tcp/1234" with
  | .ok v1, .ok draft, .ok tcp =>
    r.check "quic address: a quic-v1 multiaddr is handled" (Quic.handles v1)
    r.check "quic address: a draft-29 /quic multiaddr is not" (!Quic.handles draft)
    r.check "quic address: a tcp multiaddr is not" (!Quic.handles tcp)
    r.check "quic address: a quic-v1 multiaddr survives the socket address"
      (((Quic.socketAddress? v1).bind Quic.multiaddrOf) == some v1)
  | _, _, _ => r.check "quic address: the sample multiaddrs parse" false

/-! ## The engine -/

private def echoChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  r.check "quic: the listener has a port" (Quic.handles l.addr)
  let (d, a) ← pair l ctxD
  r.check "quic: both sides select the ALPN" (d.alpn == "quic-test" && a.alpn == "quic-test")
  r.check "quic: both sides hold the peer's certificate"
    (d.peerCertificate.size > 0 && a.peerCertificate.size > 0)
  let echo ← (Conc.Wrap.spawn (echoAll a) : BaseIO (Task (Except IO.Error Unit)))
  -- A small echo, after our FIN.
  let s ← expectOk "open" (← d.openStream)
  discard <| s.write "hello".toUTF8
  s.close
  let (got, err) ← readAll s
  r.check "quic: the peer's reply arrives after our FIN" (got == "hello".toUTF8 && err.isNone)
  -- Past the send cap and the largest stream window: 12 MiB.
  let big := pattern (12 * 1024 * 1024)
  let s ← expectOk "open" (← d.openStream)
  let writer ← (Conc.Wrap.spawn (do discard <| s.write big; s.close) :
    BaseIO (Task (Except IO.Error Unit)))
  let (got, err) ← readAll s
  discard <| Conc.Wrap.await writer
  r.check "quic: 12 MiB cross the windows whole" (got == big && err.isNone)
  -- Many streams at once.
  let results ← OnceRef.new (0 : Nat)
  let many ← TaskSet.new
  for k in List.range 32 do
    many.spawn do
      let s ← expectOk "open" (← d.openStream)
      let data := pattern (1000 + k)
      discard <| s.write data
      s.close
      let (got, _) ← readAll s
      if got == data then results.update (· + 1)
  many.joinAll
  r.check "quic: 32 streams at once each echo" ((← (results.get : BaseIO Nat)) == 32)
  -- The dialer's close: both joins answer an orderly end, and the echo
  -- task sees the end of the accept queue.
  d.close Quic.orderlyClose "done"
  r.check "quic: the dialer's join answers an orderly end" ((← d.join) matches .ok ())
  r.check "quic: the listener's connection ends in order" ((← a.join) matches .ok ())
  r.check "quic: the peer's accept queue ends" ((← Conc.Wrap.await echo) matches .ok ())
  -- The listener closes, and ends with no connection left.
  l.close
  r.check "quic: a closed listener's accept answers none" ((← acceptConn l).isNone)
  let joined ← (Conc.Wrap.spawn l.join : BaseIO (Task (Except IO.Error Unit)))
  r.check "quic: the listener's join ends" ((← Conc.Wrap.await joined) matches .ok ())

/-- The resets (RFC 9000 §3). Our reset ends both directions at once,
and the bytes that wait in the inbox go. The peer's reset sends
RESET_STREAM and STOP_SENDING, so our reads and our writes end. -/
private def resetChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  let (d, a) ← pair l ctxD
  -- Our reset with bytes in the inbox: the peer writes, we read
  -- nothing, then reset; the next read answers `.reset`, and the bytes
  -- are gone.
  let s ← expectOk "open" (← d.openStream)
  discard <| s.write "x".toUTF8
  let some sa ← a.accept | throw <| IO.userError "accept"
  let (first, _) ← match ← sa.read with
    | .ok (some b) => pure (b, ())
    | _ => throw <| IO.userError "read"
  r.check "quic reset: the peer's stream reads our byte" (first == "x".toUTF8)
  discard <| sa.write (pattern 1000)
  -- The reply is in flight; the reset must drop whatever has arrived.
  select #[← Park.sleep 100 ()]
  s.reset
  r.check "quic reset: a read after our reset answers reset at once"
    ((← s.read) matches .error .reset)
  r.check "quic reset: a write after our reset fails" ((← s.write "y".toUTF8) matches .error _)
  -- The peer's reset: our reads end with `.reset`, and so do our
  -- writes, once its STOP_SENDING arrives.
  let s ← expectOk "open" (← d.openStream)
  discard <| s.write "x".toUTF8
  let some sb ← a.accept | throw <| IO.userError "accept"
  discard sb.read
  sb.reset
  r.check "quic reset: the peer's reset ends our reads" ((← s.read) matches .error .reset)
  -- STOP_SENDING may arrive after RESET_STREAM; a write before it can
  -- still pass, so the check waits for the first refused write, for up
  -- to 5 s.
  let mut refused := false
  for _ in List.range 250 do
    if (← s.write "z".toUTF8) matches .error .reset then
      refused := true
      break
    select #[← Park.sleep 20 ()]
  r.check "quic reset: the peer's STOP_SENDING ends our writes" refused
  closeBoth d a
  l.close
  l.join

/-- The same echo over IPv6 loopback: the address bytes of the shim
carry the 16-byte form, and the dial binds `::`. -/
private def ipv6Checks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  -- A host with no IPv6 loopback cannot bind `::1`: that is the host's
  -- configuration, so the check records a skip with the reason.
  let bound : Option Listener ← try some <$> listenAny ctxL "/ip6/::1/udp/0/quic-v1"
    catch e => do
      r.skip "quic ipv6: the echo over ::1" s!"this host cannot bind ::1: {e}"
      pure none
  let some l := bound | return
  r.check "quic ipv6: the listener serves an ip6 address"
    (l.addr.components.head?.map (·.proto) == some .«ip6»)
  let (d, a) ← pair l ctxD
  let echo ← (Conc.Wrap.spawn (echoAll a) : BaseIO (Task (Except IO.Error Unit)))
  let s ← expectOk "open" (← d.openStream)
  discard <| s.write "over ipv6".toUTF8
  s.close
  let (got, _) ← readAll s
  r.check "quic ipv6: a stream echoes" (got == "over ipv6".toUTF8)
  r.check "quic ipv6: the peer's address is ip6"
    (a.remoteAddr.components.head?.map (·.proto) == some .«ip6»)
  closeBoth d a
  discard <| Conc.Wrap.await echo
  l.close
  l.join

/-- A listener that closes with a live connection: its join waits for
that connection, and ends with it. -/
private def listenerChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  let (d, a) ← pair l ctxD
  l.close
  r.check "quic: a listener closed with a live connection accepts none"
    ((← acceptConn l).isNone)
  let joined ← (Conc.Wrap.spawn l.join : BaseIO (Task (Except IO.Error Unit)))
  -- Real time: the join has 100 ms to end early, and must not.
  select #[← Park.sleep 100 ()]
  r.check "quic: the listener's join waits for its last connection"
    (!(← IO.hasFinished joined))
  closeBoth d a
  r.check "quic: the listener's join ends with its last connection"
    ((← Conc.Wrap.await joined) matches .ok ())

/-- One connection that opens and closes on a listener of its own. The
answer is the listener's address; no value that holds the endpoint
outlives the call. -/
private def oneConnection (ctxL ctxD : Tls.Context) : Async Multiformats.Multiaddr := do
  let l ← listenAny ctxL
  let (d, a) ← pair l ctxD
  closeBoth d a
  l.close
  l.join
  return l.addr

/-- An ended endpoint releases its UDP socket: a new listener binds the
port of one that has ended. The socket closes with its last reference,
so a reader whose receive was cancelled would keep the port for the life
of the process (`Quic/Loop.lean`, `stopReading`). libuv closes the
socket on its own loop, after the last reference goes, so the bind
retries for up to 5 s. -/
private def releaseChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let addr ← oneConnection ctxL ctxD
  let mut bound := false
  for _ in List.range 250 do
    try
      let l ← Quic.listen ctxL addr (Quic.admitAll acceptAny)
      l.close
      l.join
      bound := true
      break
    catch _ =>
      select #[← Park.sleep 20 ()]
  r.check "quic: an ended listener's port binds again" bound

/-- Every endpoint holds its port alone (`QuicNative.udpBind`). The
`Std.Async.UDP` bind sets SO_REUSEADDR, and with it two sockets can hold
one port (the package ARCHITECTURE, "Decisions", the exclusive bind).
So a second listen on a live listener's address fails. A socket that
`Std` binds, with its reuse option, cannot take the port of a live
listener or of a live dial either. -/
private def exclusiveChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  let (d, a) ← pair l ctxD
  let second ← try
      let l2 ← Quic.listen ctxL l.addr (Quic.admitAll acceptAny)
      l2.close
      l2.join
      pure false
    catch _ => pure true
  r.check "quic: a second listen on a live listener's address fails" second
  -- The `Std` bind, as any other socket of the process would take a port.
  let stdBinds (m : Multiformats.Multiaddr) : Async Bool := do
    let some sa := Quic.socketAddress? m | return true
    let s ← Std.Async.UDP.Socket.mk
    try
      s.bind sa
      pure true
    catch _ => pure false
  r.check "quic: a reusing socket cannot take a live listener's port"
    !(← stdBinds l.addr)
  r.check "quic: a reusing socket cannot take a live dial's port"
    !(← stdBinds d.localAddr)
  d.close Quic.orderlyClose "done"
  discard d.join
  discard a.join
  l.close
  l.join

/-- A listener whose accept queue is full refuses the next connection
with CONNECTION_REFUSED (RFC 9000 §20.1), as quic-go's server does. The
check dials one connection more than the queue holds, and accepts
nothing. The listener offers each connection when its own side of the
handshake ends, in an order no test fixes. So the check names no dial:
exactly one of them is refused, and the rest wait in the queue. -/
private def backlogChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  -- A refusal can reach a dial before its handshake answers.
  let mut refusedAtDial := 0
  let mut conns : Array Quic.Conn := #[]
  for _ in List.range (Quic.listenBacklog + 1) do
    match ← Quic.dial ctxD l.addr acceptAny with
    | .ok c => conns := conns.push c
    | .error (.peerFailed code _) =>
      if code == Quic.connectionRefused then refusedAtDial := refusedAtDial + 1
    | .error e => throw <| IO.userError s!"dial: {e}"
  -- Each join as a task: the refused connection's join ends on its own,
  -- and the others wait for the closes below.
  let joins ← conns.mapM fun c =>
    (Conc.Wrap.spawn c.join : BaseIO (Task (Except IO.Error (Except Quic.Error Unit))))
  -- Wait for the refusal. The listener refuses only once its queue is
  -- full, so at that point every handshake has ended. 10 s bounds a run
  -- that never sees one.
  for _ in List.range 500 do
    let mut ended := refusedAtDial
    for t in joins do
      if ← IO.hasFinished t then ended := ended + 1
    if ended > 0 then break
    select #[← Park.sleep 20 ()]
  for c in conns do c.close Quic.orderlyClose "done"
  let mut refused := refusedAtDial
  let mut orderly := 0
  for t in joins do
    match ← Conc.Wrap.await t with
    | .ok (.ok ()) => orderly := orderly + 1
    | .ok (.error (.peerFailed code _)) =>
      if code == Quic.connectionRefused then refused := refused + 1
    | _ => pure ()
  r.check "quic: a full accept queue refuses one connection with CONNECTION_REFUSED" (refused == 1)
  r.check "quic backlog: each other dialer's join answers an orderly end"
    (orderly == Quic.listenBacklog)
  -- The queued connections end with their dialers; the listener's
  -- close leaves them in the queue for `accept`.
  l.close
  let mut drained := 0
  let mut ended := 0
  repeat
    let some a ← acceptConn l | break
    drained := drained + 1
    if (← a.join) matches .ok () then ended := ended + 1
  r.check "quic backlog: the closed listener still gives the queued connections"
    (drained == Quic.listenBacklog)
  r.check "quic backlog: each queued connection ended with its dialer" (ended == drained)
  l.join
  r.check "quic backlog: the listener joins" true

/-- The handshake deadline (root §5.4), on the test clock: a dial to a
UDP socket that never answers ends with `.timeout` once the clock passes
`handshakeTimeoutMs`. -/
private def deadlineChecks (r : Runner) : Async Unit := do
  let ctx ← context
  let silent ← Std.Async.UDP.Socket.mk
  silent.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  let some addr := Quic.multiaddrOf (← silent.getSockName) | throw <| IO.userError "address"
  let tc ← TestClock.new
  -- The dial's answer closes the clock, so a `nextTimer` that would
  -- wait for a timer of an ended dial wakes with `false`.
  let dial ← (Conc.Wrap.spawn (try Quic.dial ctx addr acceptAny tc.clock finally tc.close) :
    BaseIO (Task (Except IO.Error (Except Quic.Error Quic.Conn))))
  -- The loop arms its first timer once the Initial is out. One second
  -- before the deadline, that timer fires, the loop sends its probe, and
  -- it arms the next timer, due at the deadline at the latest: the
  -- shim's expiry includes the handshake deadline
  -- (`ngtcp2_conn_get_expiry2`). The second `nextTimer` returns once the
  -- loop has armed it, so the loop has run that turn.
  let first ← tc.nextTimer
  tc.advance (Quic.handshakeTimeoutMs - 1000)
  let rearmed ← tc.nextTimer
  r.check "quic: one second before the handshake deadline the dial still waits"
    (first && rearmed && !(← IO.hasFinished dial))
  -- Past the deadline: the timer fires, and the dial ends with `.timeout`.
  tc.advance 2000
  let answer ← Conc.Wrap.await dial
  r.check "quic: a silent peer fails the dial at the handshake deadline"
    (answer matches .ok (.error .timeout))
  tc.close

/-- A silent UDP socket on loopback, and its `quic-v1` address: a peer
that never answers. -/
private def silentPeer : Async (Std.Async.UDP.Socket × Multiformats.Multiaddr) := do
  let silent ← Std.Async.UDP.Socket.mk
  silent.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  let some addr := Quic.multiaddrOf (← silent.getSockName) | throw <| IO.userError "address"
  return (silent, addr)

/-- The abort of a dial (root §5.5): the close of the abort channel ends
a dial still in its handshake with `.ended`, long before the 30 s
deadline would end it with `.timeout`. -/
private def abortChecks (r : Runner) : Async Unit := do
  let ctx ← context
  let (_silent, addr) ← silentPeer
  let abort : Chan Unit ← Chan.new 1
  let dial ← (Conc.Wrap.spawn (Quic.dial ctx addr acceptAny Clock.system (some abort)) :
    BaseIO (Task (Except IO.Error (Except Quic.Error Quic.Conn))))
  select #[← Park.sleep 50 ()]
  abort.close
  r.check "quic: an abort ends a dial still in its handshake"
    ((← Conc.Wrap.await dial) matches .ok (.error .ended))

/-- The loop arms a timer only when the shim's earliest timer changes
(`Conc.Alarm`). A listener with no connection has no timer, so 200
datagrams that open none arm nothing. One connection follows them: the
reader keeps the datagrams in order, so the loop has taken every one
before the connection's first. The count of the clock's `after` calls
then covers the junk and one short connection. A loop that armed a
timer on each turn would count one per datagram at least. -/
private def timerChecks (r : Runner) : Async Unit := do
  let armed ← OnceRef.new (0 : Nat)
  let counting : Clock := {
    nowMs := Clock.system.nowMs
    after := fun ms => do
      armed.update (· + 1)
      Clock.system.after ms }
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL (clock := counting)
  let some sa := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let junk ← Std.Async.UDP.Socket.mk
  junk.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  for _ in List.range 200 do
    junk.send (pattern 40) (some sa)
  let (d, a) ← pair l ctxD
  closeBoth d a
  l.close
  l.join
  r.check "quic: datagrams that open no connection arm no timer"
    ((← (armed.get : BaseIO Nat)) < 100)

/-- The stream credit of the peer returns once its stream is over and
accepted, as quic-go's does. The dialer opens `maxStreamsBidi` streams
and resets each, so each ends on the listener while it waits in the
accept queue. The next open then waits, and one accept lets it through:
the credit came back at the accept. -/
private def creditChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  let (d, a) ← pair l ctxD
  for _ in List.range Quic.maxStreamsBidi do
    let s ← expectOk "open" (← d.openStream)
    discard <| s.write "x".toUTF8
    s.reset
  let next ← (Conc.Wrap.spawn d.openStream :
    BaseIO (Task (Except IO.Error (Except Quic.Error Stream))))
  -- Real time: the open has 300 ms to go through early, and must not.
  select #[← Park.sleep 300 ()]
  r.check "quic credit: a stream that ended unaccepted gives no credit"
    (!(← IO.hasFinished next))
  let some _ ← a.accept | throw <| IO.userError "accept"
  r.check "quic credit: the accept returns the credit"
    ((← Conc.Wrap.await next) matches .ok (.ok _))
  closeBoth d a
  l.close
  l.join

/-- A client with another ALPN name: the server refuses the handshake
with the alert `no_application_protocol`, CRYPTO_ERROR 0x178 (RFC 9001
§8.1). -/
private def alpnChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context "other"
  let l ← listenAny ctxL
  let res ← Quic.dial ctxD l.addr acceptAny
  r.check "quic: a client without the server's ALPN gets no_application_protocol"
    (res matches .error (.peerFailed 0x178 _))
  l.close
  l.join

/-- A chain of two certificates fails the handshake in both directions
("Endpoints MUST abort the connection attempt if more than one
certificate is received", `vendor/specs/tls/tls.md`). The QUIC
handshake runs on the `Tls.Context`, so its one-certificate rule holds
here too. A client sends its certificate with its last flight, so the
client may finish before the server refuses: the dial then succeeds,
and the connection's join answers the server's close. -/
private def chainChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let ctxChain ← context
  -- The certificate past the first is any other; only the count matters.
  let key ← match ← Crypto.p256Generate.run with
    | .ok k => pure k
    | .error _ => throw <| IO.userError "p256 key"
  let otherCert ← match ← (Crypto.issue key "1.3.6.1.4.1.53594.1.1" ⟨#[0x30, 0x00]⟩ false
      1500000000 2100000000).run with
    | .ok c => pure c
    | .error _ => throw <| IO.userError "issue"
  let added ← (TlsNative.addChainCertificate ctxChain.native otherCert : IO Bool)
  r.check "quic chain of two: the context takes the extra certificate" added
  -- The listener sends two certificates: the dialer refuses them.
  let l ← listenAny ctxChain
  r.check "quic chain of two: the dialer refuses the listener's chain"
    (match ← Quic.dial ctxD l.addr acceptAny with
      | .error (.refused d) => (d.splitOn "sent 2 certificates").length > 1
      | _ => false)
  l.close
  l.join
  -- The dialer sends two certificates: the listener refuses them with
  -- `bad_certificate`, and accepts no connection.
  let l ← listenAny ctxL
  let t ← (Conc.Wrap.spawn (acceptConn l) : BaseIO (Task (Except IO.Error (Option Quic.Conn))))
  let refused ← match ← Quic.dial ctxChain l.addr acceptAny with
    | .error (.peerFailed 0x12a _) => pure true
    | .error _ => pure false
    | .ok c => do pure ((← c.join) matches .error (.peerFailed 0x12a _))
  r.check "quic chain of two: the listener refuses the dialer's chain with bad_certificate" refused
  l.close
  r.check "quic chain of two: the listener accepts no connection"
    ((← Conc.Wrap.await t) matches .ok none)
  l.join

/-- An application close with a code (RFC 9000 §10.2): the closer's join
and the peer's join both answer `.closed` with that code. -/
private def closeCodeChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  let (d, a) ← pair l ctxD
  d.close 42 "bye"
  r.check "quic: our close with an application code ends our join with that code"
    ((← d.join) matches .error (.closed 42 _))
  r.check "quic: the peer's join answers the same code" ((← a.join) matches .error (.closed 42 _))
  l.close
  l.join

/-! ## Datagrams of the suite's own

The checks below put datagrams on the wire themselves. The suite
captures a client's first Initial from a real dial and sends it again
from another socket. That stands for a client whose source address
never answers: the spoofed source of RFC 9000 §8. A relay between a
dialer and a listener drops one direction or both. -/

/-- A loopback UDP socket on a port the system picks. -/
private def loopbackSocket : Async Std.Async.UDP.Socket := do
  let s ← Std.Async.UDP.Socket.mk
  s.bind (.v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, 0⟩)
  return s

/-- The datagrams `s` receives within `ms` of real time. The receive
that waits at the end wakes with an empty datagram to the socket itself;
an empty datagram is never in the answer. -/
private def received (s : Std.Async.UDP.Socket) (ms : Nat) : Async (Array ByteArray) := do
  let self ← s.getSockName
  let got ← OnceRef.new (#[] : Array ByteArray)
  let stop ← OnceRef.new false
  let t ← (Conc.Wrap.spawn (do
      repeat
        -- Park: a datagram wakes it; the wake below ends the loop.
        let (b, _) ← s.recv 65535
        if b.size > 0 then got.update (·.push b)
        else if ← (stop.get : BaseIO Bool) then break) :
    BaseIO (Task (Except IO.Error Unit)))
  select #[← Park.sleep ms ()]
  stop.set true
  s.send .empty (some self)
  discard <| Conc.Wrap.await t
  got.get

/-- The first datagram of each of `n` dials, each to a silent socket of
its own: the first Initials of `n` distinct connections. Each dial ends
by its abort once its Initial has arrived. -/
private def captureInitials (ctx : Tls.Context) (n : Nat) : Async (Array ByteArray) := do
  let mut out := #[]
  for _ in List.range n do
    let (silent, addr) ← silentPeer
    let abort : Chan Unit ← Chan.new 1
    let dial ← (Conc.Wrap.spawn (Quic.dial ctx addr acceptAny Clock.system (some abort)) :
      BaseIO (Task (Except IO.Error (Except Quic.Error Quic.Conn))))
    let (b, _) ← silent.recv 65535
    out := out.push b
    abort.close
    discard <| Conc.Wrap.await dial
  return out

/-- The packet type of a long header (RFC 9000 §17.2): the two bits
after the header form and the fixed bit. Header protection leaves them
in the clear. -/
private def longType (b : ByteArray) : Option UInt8 :=
  if b.size > 0 && b[0]! &&& 0xC0 == 0xC0 then some ((b[0]! >>> 4) &&& 0x3) else none

/-- The type of an Initial packet (RFC 9000 §17.2, Table 5). -/
private def initialType : UInt8 := 0x0

/-- The type of a Retry packet (RFC 9000 §17.2, Table 5). -/
private def retryType : UInt8 := 0x3

/-- An Initial with the token `token` in place of its empty one. The
token sits after the two connection IDs (RFC 9000 §17.2.2), and a
token of fewer than 64 bytes takes a one-byte length. -/
private def withToken (b : ByteArray) (token : ByteArray) : ByteArray :=
  let dcidLen := b[5]!.toNat
  let at_ := 7 + dcidLen + b[6 + dcidLen]!.toNat
  b.extract 0 at_ ++ ⟨#[token.size.toUInt8]⟩ ++ token ++ b.extract (at_ + 1) b.size

/-- The admission of a listener (`Quic.Admitted`): a refusal answers the
client with CONNECTION_REFUSED before any state exists; a connection
whose handshake fails releases its admission; a connection the listener
hands over is the receiver's, and the endpoint releases nothing. -/
private def admissionChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let asked ← OnceRef.new (0 : Nat)
  let refusing (_ _ : Multiformats.Multiaddr) : BaseIO (Option (Quic.Admitted Unit)) := do
    asked.update (· + 1)
    return none
  let l ← Quic.listen ctxL (← ma "/ip4/127.0.0.1/udp/0/quic-v1") refusing
  r.check "quic admission: a refused client gets CONNECTION_REFUSED"
    ((← Quic.dial ctxD l.addr acceptAny) matches .error (.peerFailed 0x2 _))
  r.check "quic admission: the listener asked its caller" ((← (asked.get : BaseIO Nat)) ≥ 1)
  l.close
  l.join
  let released ← OnceRef.new (0 : Nat)
  let counting (_ _ : Multiformats.Multiaddr) : BaseIO (Option (Quic.Admitted Unit)) :=
    pure (some { check := acceptAny, value := (), release := released.update (· + 1) })
  let l ← Quic.listen ctxL (← ma "/ip4/127.0.0.1/udp/0/quic-v1") counting
  -- A client with another ALPN fails its handshake (RFC 9001 §8.1).
  discard <| Quic.dial (← context "other") l.addr acceptAny
  let mut n := 0
  for _ in List.range 250 do
    n ← (released.get : BaseIO Nat)
    if n > 0 then break
    select #[← Park.sleep 20 ()]
  r.check "quic admission: a failed handshake releases its admission" (n == 1)
  let (d, a) ← pair l ctxD
  closeBoth d a
  r.check "quic admission: a handed-over connection releases nothing"
    ((← (released.get : BaseIO Nat)) == 1)
  l.close
  l.join

/-- The cap on connections in their handshake (`Quic.maxHandshakes`):
three Initials from a source that never answers fill a cap of three,
and the next client gets CONNECTION_REFUSED, with no state kept. -/
private def capChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let initials ← captureInitials ctxD 3
  let l ← listenAny ctxL (bounds := { maxHandshakes := 3, retryThreshold := 3 })
  let some sa := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let spoof ← loopbackSocket
  for b in initials do spoof.send b (some sa)
  -- The listener answers each one: three connections are in their
  -- handshake, and the dial below comes after them.
  let answers ← received spoof 300
  r.check "quic cap: the listener answers the Initials within the cap" (answers.size ≥ 3)
  r.check "quic cap: a client past the cap gets CONNECTION_REFUSED"
    ((← Quic.dial ctxD l.addr acceptAny) matches .error (.peerFailed 0x2 _))
  l.close
  l.join

/-- The Retry past the threshold (RFC 9000 §8.1.2; `Quic.retryThreshold`).
With a threshold of two and a cap of three, twelve spoofed Initials
open two connections. The other ten get a Retry each, so they keep no
state. A real client answers its Retry, proves its address, and
connects. The cap of three still has room for it. It would have none
if a spoofed Initial past the threshold had opened a connection. -/
private def retryChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let initials ← captureInitials ctxD 12
  let l ← listenAny ctxL (bounds := { maxHandshakes := 3, retryThreshold := 2 })
  let some sa := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let spoof ← loopbackSocket
  for b in initials do spoof.send b (some sa)
  let answers ← received spoof 500
  r.check "quic retry: past the threshold each spoofed Initial gets a Retry"
    ((answers.filter (longType · == some retryType)).size == 10)
  let connected ← match ← Quic.dial ctxD l.addr acceptAny with
    | .ok c => do
      c.close Quic.orderlyClose "done"
      pure ((← c.join) matches .ok ())
    | .error _ => pure false
  r.check "quic retry: a real client answers the Retry and connects" connected
  l.close
  l.join

/-- A forged Retry token (RFC 9000 §8.1.2): the Initial gets one close,
in an Initial packet with no state behind it, and a connection never
opens. A connection would answer with its handshake, several datagrams
of more than a thousand bytes. -/
private def tokenChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let initials ← captureInitials ctxD 1
  let l ← listenAny ctxL
  let some sa := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let spoof ← loopbackSocket
  -- The token starts with the magic byte of ngtcp2's Retry tokens, 0xB7,
  -- so the listener checks it, and the check fails.
  spoof.send (withToken initials[0]! ⟨#[0xB7] ++ Array.replicate 40 0x55⟩) (some sa)
  let answers ← received spoof 300
  r.check "quic token: a forged Retry token gets one Initial and no connection"
    (answers.size == 1 && longType answers[0]! == some initialType && answers[0]!.size < 600)
  l.close
  l.join

/-- The closing period of a connection the listener closed (RFC 9000
§10.2): a packet for it gets the close again, and past
`maxClosingPeriods` records the oldest goes. One live connection keeps
the endpoint up after the listener's close, which refuses the two
handshakes of the spoofed Initials. With room for one record, exactly
one of the two Initials, sent again, gets an answer. -/
private def closingChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let initials ← captureInitials ctxD 2
  let l ← listenAny ctxL (bounds := { maxClosingPeriods := 1 })
  let (d, a) ← pair l ctxD
  let some sa := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let spoof ← loopbackSocket
  for b in initials do spoof.send b (some sa)
  discard <| received spoof 300
  l.close
  -- The two closes of the listener's close.
  discard <| received spoof 300
  spoof.send initials[0]! (some sa)
  let first ← received spoof 300
  spoof.send initials[1]! (some sa)
  let second ← received spoof 300
  r.check "quic closing: one record answers its packet with the close again, the other is gone"
    (first.size + second.size == 1)
  closeBoth d a
  l.join

/-- A client whose version the listener does not speak gets a version
negotiation packet (RFC 9000 §6.1, §17.2.1): version 0, the client's
IDs swapped, and QUIC v1 (`0x00000001`) as the one version listed. The
client's datagram is a long header of 1200 bytes (RFC 9000 §14.1). -/
private def versionChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let l ← listenAny ctxL
  let some sa := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let spoof ← loopbackSocket
  let header : Array UInt8 :=
    #[0xC0, 0x1a, 0x2a, 0x3a, 0x4a, 8] ++ Array.replicate 8 0x11 ++ #[8] ++ Array.replicate 8 0x22
  spoof.send ⟨header ++ Array.replicate (1200 - header.size) 0⟩ (some sa)
  let answers ← received spoof 300
  let vn := answers[0]!
  r.check "quic: an unknown version gets a version negotiation that lists QUIC v1"
    (answers.size == 1 && vn.extract 1 5 == ⟨#[0, 0, 0, 0]⟩ &&
      vn.extract 5 15 == ⟨#[8] ++ Array.replicate 8 0x22 ++ #[8]⟩ &&
      vn.extract (vn.size - 4) vn.size == ⟨#[0, 0, 0, 1]⟩)
  l.close
  l.join

/-- A UDP relay between one dialer and the listener at `target`: the
dialer dials `addr`, and each datagram passes unless its direction is
cut. -/
private structure Relay where
  addr : Multiformats.Multiaddr
  /-- Drop the listener's datagrams. -/
  cutToDialer : OnceRef Bool
  /-- Drop the dialer's datagrams. -/
  cutToListener : OnceRef Bool
  /-- End the relay and join its task. -/
  stop : Async Unit

/-- A relay on loopback (`Relay`). -/
private def relay (target : Std.Net.SocketAddress) : Async Relay := do
  let s ← loopbackSocket
  let self ← s.getSockName
  let some addr := Quic.multiaddrOf self | throw <| IO.userError "relay address"
  let cutToDialer ← OnceRef.new false
  let cutToListener ← OnceRef.new false
  let stopped ← OnceRef.new false
  let dialer : OnceRef (Option Std.Net.SocketAddress) ← OnceRef.new none
  let t ← (Conc.Wrap.spawn (do
      repeat
        -- Park: a datagram wakes it, and so does the stop's own datagram.
        let (b, src) ← s.recv 65535
        if ← (stopped.get : BaseIO Bool) then break
        let some src := src | continue
        if src == target then
          if !(← (cutToDialer.get : BaseIO Bool)) then
            if let some d ← (dialer.get : BaseIO (Option Std.Net.SocketAddress)) then
              s.send b (some d)
        else
          dialer.set (some src)
          if !(← (cutToListener.get : BaseIO Bool)) then s.send b (some target)) :
    BaseIO (Task (Except IO.Error Unit)))
  return { addr, cutToDialer, cutToListener
           stop := do
             stopped.set true
             s.send .empty (some self)
             discard <| Conc.Wrap.await t }

/-- The answer of `t`, while the test clock moves one millisecond per
step, with real time between the steps. Traffic on a test clock needs
its timers to come due, the pacer's among them (`ngtcp2_conn_update_pkt_tx_time`),
so a handshake or a stream on a frozen clock would wait forever. -/
private def awaitTicking {β : Type} (tc : TestClock) (t : Task (Except IO.Error β)) :
    Async β := do
  repeat
    if ← IO.hasFinished t then break
    tc.advance 1
    select #[← Park.sleep 5 ()]
  match ← Conc.Wrap.await t with
  | .ok v => return v
  | .error e => throw e

/-- The idle timeout (RFC 9000 §10.1), on the test clock: after the
handshake the relay drops every datagram, and the dialer's connection
ends with `.idle` once its clock has passed `idleTimeoutMs`. -/
private def idleChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  let some target := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let rl ← relay target
  let tc ← TestClock.new
  let t ← (Conc.Wrap.spawn (acceptConn l) : BaseIO (Task (Except IO.Error (Option Quic.Conn))))
  let dial ← (Conc.Wrap.spawn (Quic.dial ctxD rl.addr acceptAny tc.clock) :
    BaseIO (Task (Except IO.Error (Except Quic.Error Quic.Conn))))
  let d ← expectOk "dial" (← awaitTicking tc dial)
  -- The dialer's handshake ends when it sends its last flight, so the
  -- clock keeps moving until the listener has the connection too.
  let some a ← awaitTicking tc t | throw <| IO.userError "accept"
  rl.cutToDialer.set true
  rl.cutToListener.set true
  let joined ← (Conc.Wrap.spawn d.join : BaseIO (Task (Except IO.Error (Except Quic.Error Unit))))
  -- One second of the test clock per step, and real time between steps
  -- for the loop to take each timer.
  let mut advanced := 0
  for _ in List.range 120 do
    if ← IO.hasFinished joined then break
    tc.advance 1000
    advanced := advanced + 1000
    select #[← Park.sleep 20 ()]
  -- A connection that outlived the steps gets our close, so the join
  -- below returns, and the check fails.
  let ended ← IO.hasFinished joined
  unless ended do d.close Quic.orderlyClose "the idle timer never fired"
  r.check "quic: a silent peer ends the connection at the idle timeout"
    (ended && (← Conc.Wrap.await joined) matches .ok (.error .idle))
  r.check "quic: the idle end comes no earlier than the idle timeout"
    (advanced ≥ Quic.idleTimeoutMs)
  a.close Quic.orderlyClose "done"
  discard a.join
  l.close
  l.join
  rl.stop
  tc.close

/-- The keep-alive (`keepAliveMs`): two peers on one test clock that
send nothing for half again the idle timeout stay connected, since each
pings the other before its idle timer ends, and a stream still echoes
after it. -/
private def keepAliveChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let tc ← TestClock.new
  let l ← listenAny ctxL (clock := tc.clock)
  let t ← (Conc.Wrap.spawn (acceptConn l) : BaseIO (Task (Except IO.Error (Option Quic.Conn))))
  let dial ← (Conc.Wrap.spawn (Quic.dial ctxD l.addr acceptAny tc.clock) :
    BaseIO (Task (Except IO.Error (Except Quic.Error Quic.Conn))))
  let d ← expectOk "dial" (← awaitTicking tc dial)
  let some a ← awaitTicking tc t | throw <| IO.userError "accept"
  let joined ← (Conc.Wrap.spawn d.join : BaseIO (Task (Except IO.Error (Except Quic.Error Unit))))
  for _ in List.range (3 * Quic.idleTimeoutMs / 2 / 1000) do
    tc.advance 1000
    select #[← Park.sleep 20 ()]
  r.check "quic: the keep-alive holds an idle connection past the idle timeout"
    (!(← IO.hasFinished joined))
  let echo ← (Conc.Wrap.spawn (echoAll a) : BaseIO (Task (Except IO.Error Unit)))
  let round ← (Conc.Wrap.spawn (do
      let s ← expectOk "open" (← d.openStream)
      discard <| s.write "still here".toUTF8
      s.close
      return (← readAll s).1) : BaseIO (Task (Except IO.Error ByteArray)))
  r.check "quic: a stream echoes after the idle stretch"
    ((← awaitTicking tc round) == "still here".toUTF8)
  d.close Quic.orderlyClose "done"
  discard <| awaitTicking tc joined
  let aJoined ← (Conc.Wrap.spawn a.join : BaseIO (Task (Except IO.Error (Except Quic.Error Unit))))
  discard <| awaitTicking tc aJoined
  discard <| awaitTicking tc echo
  l.close
  l.join
  tc.close

/-- The send cap (`streamSendCap`): a write of twice the cap parks while
the peer's ACKs do not arrive, and it ends once they do. The shim keeps
every byte the peer has not acknowledged (RFC 9000 §13.3). -/
private def sendCapChecks (r : Runner) : Async Unit := do
  let ctxL ← context
  let ctxD ← context
  let l ← listenAny ctxL
  let some target := Quic.socketAddress? l.addr | throw <| IO.userError "address"
  let rl ← relay target
  let t ← (Conc.Wrap.spawn (acceptConn l) : BaseIO (Task (Except IO.Error (Option Quic.Conn))))
  let d ← expectOk "dial" (← Quic.dial ctxD rl.addr acceptAny)
  let some a ← (do match ← Conc.Wrap.await t with | .ok x => pure x | .error e => throw e)
    | throw <| IO.userError "accept"
  let echo ← (Conc.Wrap.spawn (echoAll a) : BaseIO (Task (Except IO.Error Unit)))
  let s ← expectOk "open" (← d.openStream)
  rl.cutToDialer.set true
  let w ← (Conc.Wrap.spawn (s.write (pattern (2 * Quic.streamSendCap))) :
    BaseIO (Task (Except IO.Error (Except Streams.Error Unit))))
  -- Real time: the write has 300 ms to end early, and must not.
  select #[← Park.sleep 300 ()]
  r.check "quic: a write past the send cap waits while no ACK arrives" (!(← IO.hasFinished w))
  rl.cutToDialer.set false
  r.check "quic: the write ends once the ACKs arrive" ((← Conc.Wrap.await w) matches .ok (.ok ()))
  s.close
  let (got, _) ← readAll s
  r.check "quic: the bytes past the send cap arrive whole"
    (got == pattern (2 * Quic.streamSendCap))
  closeBoth d a
  discard <| Conc.Wrap.await echo
  l.close
  l.join
  rl.stop

/-! ## The libp2p transport -/

open Libp2p.Identity in
/-- The Ed25519 host key of one byte. -/
private def hostKey (v : UInt8) : Async PrivKey := do
  let .ok key := PrivKey.ofData? .ed25519 ⟨Array.replicate 32 v⟩
    | throw <| IO.userError "test identity"
  return key

/-- A TLS configuration for an Ed25519 host key from one byte, issued
at the time `now` gives, which also becomes the clock of the validity
check. -/
private def tlsCfg (v : UInt8) (now : IO Int := Libp2p.Security.Tls.wallSeconds) :
    Async Libp2p.Security.Tls.Config := do
  let certKey ← match ← Crypto.p256Generate.run with
    | .ok k => pure k
    | .error _ => throw <| IO.userError "cert key"
  match ← Libp2p.Security.Tls.Config.ofCertKey (← hostKey v) certKey now with
  | .ok c => return c
  | .error e => throw <| IO.userError s!"tls config: {repr e}"

/-- An abort channel that no one closes: a dial that only its own
answer ends. -/
private def noAbort : BaseIO (Chan Unit) := Chan.new 1

/-- The admission of a suite that tests no policy: the default gater
and the resource manager that limits nothing. -/
private def admitAny : Libp2p.Core.Admit :=
  Libp2p.Host.Policy.admission Libp2p.Host.Policy.permissiveGater Libp2p.Host.Policy.unlimited

open Libp2p.Core in
/-- Listen through a secured transport with `admitAny`. -/
private def listenSecured (t : SecuredTransport) : Async SecuredListener := do
  t.listen (← ma "/ip4/127.0.0.1/udp/0/quic-v1") admitAny

open Libp2p.Core in
/-- The next session of a secured listener, as a task the caller
awaits. The scope of `admitAny` limits nothing, so the task drops it. -/
private def acceptTask (l : SecuredListener) :
    BaseIO (Task (Except IO.Error (Option SecuredSession))) :=
  Conc.Wrap.spawn ((·.map Prod.fst) <$> l.accept)

open Libp2p.Core in
private def transportChecks (r : Runner) : Async Unit := do
  let cfgL ← tlsCfg 21
  let cfgD ← tlsCfg 22
  let tL := Libp2p.Quic.transport cfgL
  let tD := Libp2p.Quic.transport cfgD
  let l ← listenSecured tL
  -- The dial proves the listener's peer id, and the listener the
  -- dialer's.
  let t ← acceptTask l
  let d ← match ← (tD.dial l.addr (some cfgL.localPeer) (← noAbort)).run with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"dial: {e}"
  let some a ← (do match ← Conc.Wrap.await t with | .ok x => pure x | .error e => throw e)
    | throw <| IO.userError "accept"
  r.check "libp2p quic: the dialer proves the listener's peer id" (d.remotePeer == cfgL.localPeer)
  r.check "libp2p quic: the listener proves the dialer's peer id" (a.remotePeer == cfgD.localPeer)
  r.check "libp2p quic: each side names its own peer id"
    (d.localPeer == cfgD.localPeer && a.localPeer == cfgL.localPeer)
  -- A stream over the session.
  let s ← match ← (d.session.openStream ⟨"/test"⟩).run with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"open: {e}"
  discard <| s.write "ping".toUTF8
  s.close
  let some sa ← a.session.accept | throw <| IO.userError "stream accept"
  let (got, _) ← readAll sa
  r.check "libp2p quic: a stream carries bytes" (got == "ping".toUTF8)
  d.session.close
  r.check "libp2p quic: the dialer's join answers an orderly end"
    ((← d.session.join.run) matches .ok ())
  discard a.session.join.run
  -- A dial that expects another peer fails inside the handshake with
  -- `authentication`, as go-libp2p's does; the listener gets the alert
  -- and accepts nothing.
  let wrong := (← tlsCfg 23).localPeer
  r.check "libp2p quic: an unexpected peer id fails the dial inside the handshake"
    (match ← (tD.dial l.addr (some wrong) (← noAbort)).run with
      | .error (.authentication d) => (d.splitOn "the dialer expected").length > 1
      | _ => false)
  -- A listener whose certificate expired: the dialer refuses it.
  let cfgOld ← tlsCfg 24 (pure (-6311520000))
  let lOld ← listenSecured (Libp2p.Quic.transport cfgOld)
  r.check "libp2p quic: an expired certificate fails the dial"
    (match ← (tD.dial lOld.addr none (← noAbort)).run with
      | .error (.authentication d) => (d.splitOn "expired").length > 1
      | _ => false)
  lOld.close
  lOld.join
  -- A dialer whose certificate lacks the extension: the listener's
  -- check refuses it inside the handshake, with `bad_certificate`.
  let now ← (Libp2p.Security.Tls.wallSeconds : IO Int)
  let certKey ← match ← Crypto.p256Generate.run with
    | .ok k => pure k
    | .error _ => throw <| IO.userError "cert key"
  let cert ← match ← (Crypto.issue certKey "1.3.6.1.4.1.53594.1.2" ⟨#[0, 0]⟩ false
      (now - 60) (now + 3600)).run with
    | .ok c => pure c
    | .error _ => throw <| IO.userError "issue"
  let ctx ← expectOk "context" (← Tls.Context.new cert certKey Libp2p.Security.Tls.alpn)
  let t ← acceptTask l
  -- A TLS alert travels as CRYPTO_ERROR, 0x100 plus the alert (RFC 9001
  -- §4.8). The client may finish before the server refuses.
  let refused ← match ← Quic.dial ctx l.addr acceptAny with
    | .error (.peerFailed 0x12a _) => pure true
    | .error _ => pure false
    | .ok c => do pure ((← c.join) matches .error (.peerFailed 0x12a _))
  r.check "libp2p quic: a certificate without the extension is refused with bad_certificate" refused
  l.close
  r.check "libp2p quic: a closed listener's accept answers none"
    ((← Conc.Wrap.await t) matches .ok none)
  l.join

open Libp2p.Core in
/-- A listener whose wall clock fails: the validity window cannot be
checked, so its check refuses every dialer (the module doc of
`Libp2p/Quic/Transport.lean`, "The check"). -/
private def clockChecks (r : Runner) : Async Unit := do
  let cfgL := { (← tlsCfg 25) with now := throw (IO.userError "no clock") }
  let cfgD ← tlsCfg 26
  let l ← listenSecured (Libp2p.Quic.transport cfgL)
  let t ← acceptTask l
  let refused ← match ← (Libp2p.Quic.transport cfgD).dial l.addr none (← noAbort) |>.run with
    | .error (.protocol _) => pure true
    | .error _ => pure false
    | .ok s => do pure ((← s.session.join.run) matches .error (.protocol _))
  r.check "libp2p quic: a listener whose wall clock fails refuses the dialer" refused
  l.close
  r.check "libp2p quic: that listener accepts no session" ((← Conc.Wrap.await t) matches .ok none)
  l.join

open Libp2p.Core in
/-- The test value: fixed keys and a fixed clock prove the same peer
ids in two runs. -/
private def fixedChecks (r : Runner) : Async Unit := do
  let certKey ← match ← Crypto.p256Generate.run with
    | .ok k => pure k
    | .error _ => throw <| IO.userError "cert key"
  let wall ← (Libp2p.Security.Tls.wallSeconds : IO Int)
  let run : Async (Option Libp2p.Identity.PeerId) := do
    let tL ← expectOk "fixed" ((← Libp2p.Quic.fixedKeyTransport (← hostKey 41) certKey wall).mapError
      fun e => reprStr e)
    let tD ← expectOk "fixed" ((← Libp2p.Quic.fixedKeyTransport (← hostKey 42) certKey wall).mapError
      fun e => reprStr e)
    let l ← listenSecured tL
    let t ← acceptTask l
    let peer ← match ← (tD.dial l.addr none (← noAbort)).run with
      | .ok s =>
        s.session.close
        discard s.session.join.run
        pure (some s.remotePeer)
      | .error _ => pure none
    -- The dial ends when ngtcp2 reports the client's handshake, before
    -- the client's Finished leaves; the pacer can hold that packet to the
    -- next millisecond. A close in that gap ends the connection inside
    -- the server's handshake (RFC 9000 §10.2.3), and the listener never
    -- offers it. So the listener closes first, and its accept then
    -- answers the session it holds, or none.
    l.close
    match ← Conc.Wrap.await t with
    | .ok (some a) => discard a.session.join.run
    | _ => pure ()
    l.join
    return peer
  let want ← expectOk "peer id" ((← hostKey 41).toPublic.bind Libp2p.Identity.PeerId.ofPubKey
    |>.mapError fun e => reprStr e)
  let first ← run
  let second ← run
  r.check "libp2p quic fixed value: the dial proves the fixed peer id" (first == some want)
  r.check "libp2p quic fixed value: a second run proves the same peer id" (second == first)

/-- The ranker puts QUIC first. -/
private def rankerChecks (r : Runner) : Async Unit := do
  let tcp ← ma "/ip4/10.0.0.1/tcp/9000"
  let quic ← ma "/ip4/10.0.0.1/udp/9000/quic-v1"
  let order := (Libp2p.Host.Policy.quicFirst.rank [tcp, quic]).map (·.addr)
  r.check "host: the default ranker puts the QUIC address first" (order == [quic, tcp])

open Libp2p.Host in
/-- Two hosts over QUIC only: a dial by address and peer id, and a
ping. -/
private def hostChecks (r : Runner) : Async Unit := do
  let mk (v : UInt8) : Async Host := do
    let cfg ← tlsCfg v
    match ← (Host.new {
        identity := ← hostKey v
        transports := []
        securedTransports := [Libp2p.Quic.transport cfg]
        security := []
        muxers := []
        handlers := [Libp2p.Protocols.Ping.pingHandler] } : BaseIO _) with
    | .ok h => return h
    | .error _ => throw <| IO.userError "host"
  let server ← mk 31
  let client ← mk 32
  let .ok bound ← server.startListening (← ma "/ip4/127.0.0.1/udp/0/quic-v1")
    | throw <| IO.userError "listen"
  match ← client.dial bound (some server.localPeer) with
  | .ok p => r.check "host quic: the client dials the server's peer" (p == server.localPeer)
  | .error e => r.check s!"host quic: the dial succeeds ({repr e})" false
  match ← client.newStream server.localPeer [Libp2p.Protocols.Ping.protocolId] with
  | .ok (_, s) =>
    let rtt ← Libp2p.Protocols.Ping.ping s Clock.system ⟨Array.replicate 32 7⟩
    r.check "host quic: a ping over QUIC echoes" (rtt matches .ok (some _))
    s.close
  | .error e => r.check s!"host quic: the ping stream opens ({repr e})" false
  r.check "host quic: the server serves the client's peer"
    (← (server.connected client.localPeer : BaseIO Bool))
  -- `Host.close` throws the fault of a joined task, so each close is a
  -- check.
  let closes (h : Host) : Async Bool := do
    try
      h.close
      return true
    catch _ => return false
  -- A QUIC dial still in its handshake when the host closes: the close
  -- ends it (root §5.5), long before its 30 s deadline would.
  let (_silent, silentAddr) ← silentPeer
  let pending ← (Conc.Wrap.spawn (client.dial silentAddr) :
    BaseIO (Task (Except IO.Error (Except Libp2p.Host.Error Libp2p.Identity.PeerId))))
  select #[← Park.sleep 50 ()]
  let start ← (IO.monoMsNow : BaseIO Nat)
  r.check "host quic: the client closes with no fault" (← closes client)
  let answer ← Conc.Wrap.await pending
  let took := (← (IO.monoMsNow : BaseIO Nat)) - start
  r.check "host quic: the close ends a QUIC dial still in its handshake"
    ((answer matches .ok (.error _)) && took < 10000)
  r.check "host quic: the server closes with no fault" (← closes server)

/-- The suite. -/
def run (r : Runner) : IO Unit := do
  r.section "QUIC (W4.4)" "RFC 9000; RFC 9001; ngtcp2 v1.24.0; libp2p/specs quic/README.md"
  addressChecks r
  Async.run do
    echoChecks r
    resetChecks r
    ipv6Checks r
    listenerChecks r
    releaseChecks r
    exclusiveChecks r
    backlogChecks r
    deadlineChecks r
    abortChecks r
    timerChecks r
    creditChecks r
    alpnChecks r
    chainChecks r
    closeCodeChecks r
    admissionChecks r
    capChecks r
    retryChecks r
    tokenChecks r
    closingChecks r
    versionChecks r
    idleChecks r
    keepAliveChecks r
    sendCapChecks r
    transportChecks r
    clockChecks r
    fixedChecks r
    rankerChecks r
    hostChecks r

end Tests.QuicSuite
