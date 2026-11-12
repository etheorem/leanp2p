import Streams
import Crypto
import Tls
import TlsNative
import Quic
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Security
import Libp2p.Quic
import Libp2p.Host
import Libp2p.Protocols.Identify

/-!
# The QUIC interop driver (unit W4.4)

The Lean side of the QUIC interop check against go-libp2p v0.50.0's own
host with its QUIC transport (`p2p/transport/quic`, quic-go v0.62.0
under it). `scripts/quic-interop.sh` builds the go side
(`scripts/quic-interop/`) and runs both directions over loopback UDP.
Our side runs a `Host` with `Libp2p.Quic.transport` as its one secured
transport, and no TCP transport, as `cli/` assembles it.

* `quic-interop listen`: serve `/test/echo` and `/test/done`, print the
  port, and close after `/test/done` has ended.
* `quic-interop dial PORT`: dial
  `/ip4/127.0.0.1/udp/PORT/quic-v1/p2p/<go id>`, open a stream that
  proposes `/test/unknown` and then `/test/echo`, check the echo, then
  open `/test/done`, read `bye`, and close.
* `quic-interop dial-refused PORT`: two dials that go must refuse,
  then the dial above.
* `quic-interop dial-handshake PORT` and `dial-badcert PORT`: the
  dials of the go servers of `refuse.go` (the section "The
  refusals").

Both directions run the libp2p TLS handshake inside QUIC: each side
checks the other's certificate and the peer id it derives, inside the
handshake.

The ending fixes who closes first. The listener answers `/test/done`
with `bye`, then reads that stream until the dialer's close of its host
ends it, and only then closes its own host. So no side tears down a
session that the other is still using.

Each side checks that the other proved the peer id of its fixed seed.
The go host runs identify on each connection, and this host answers it
with `Identify.respondHandler`: its listen address, its protocols, and
`leanAgent`. The go side waits for that identify and checks the agent
and the protocols it recorded. Every failure that reaches
`Config.onFailure` fails the run.

The driver lives outside `lake test`, which stays hermetic: Go tooling
is test-only and confined to the harness (CLAUDE.md, "Dependencies").
The seeds and the payload pattern match the go side.
-/

set_option autoImplicit false

namespace Tests.Interop.Quic

open Conc (Async Chan OnceRef Clock)
open Libp2p.Identity Libp2p.Core Libp2p.Security
open Libp2p.Host (Host Config Failure)

/-- 32 bytes of one value, the form of both identity seeds. -/
def seed (v : UInt8) : ByteArray := ⟨Array.replicate 32 v⟩

/-- Our identity seed: 32 bytes of `H`. The go side holds the same. -/
def leanSeed : ByteArray := seed 'H'.toNat.toUInt8

/-- The go side's identity seed: 32 bytes of `G`. -/
def goSeed : ByteArray := seed 'G'.toNat.toUInt8

/-- The bytes of the echo: 2 MiB. Both sides start with quic-go's
windows, 512 KiB for a stream and 768 KiB for the connection
(`Quic.streamWindow`, `Quic.connWindow`), so the echo passes only when
each receiver sends window updates. It is also past our
`Quic.streamSendCap`, so our writes park until go acknowledges. -/
def size : Nat := 2 * 1024 * 1024

/-- The pattern both sides build. -/
def payload (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun k => UInt8.ofNat ((k * 7 + 3) % 251)⟩

/-- The protocols of the check. The `/test/` prefix keeps them apart
from every real id. -/
def echoId : ProtocolId := ⟨"/test/echo"⟩
def doneId : ProtocolId := ⟨"/test/done"⟩
def unknownId : ProtocolId := ⟨"/test/unknown"⟩

/-- Fail with a message. -/
def fail {α : Type} (msg : String) : Async α :=
  throw <| IO.userError s!"lean: {msg}"

/-- The value of an `Except`, or a failure that names the error. -/
def orFail {ε α : Type} [ToString ε] (what : String) : Except ε α → Async α
  | .ok a => return a
  | .error e => fail s!"{what}: {e}"

/-- A multiaddr from its text form. -/
def addr (s : String) : Async Multiformats.Multiaddr := do
  orFail s!"address {s}" (Multiformats.Multiaddr.parse? s |>.mapError fun e => repr e |>.pretty)

/-- The Ed25519 key of a seed. -/
def keyOf (s : ByteArray) : Async PrivKey :=
  orFail "identity" (PrivKey.ofData? .ed25519 s |>.mapError fun e => (repr e).pretty)

/-- The public key of a seed. -/
def pubOf (s : ByteArray) : Async PubKey := do
  orFail "public key" ((← keyOf s).toPublic |>.mapError fun e => (repr e).pretty)

/-- The peer id of a seed. -/
def peerOfSeed (s : ByteArray) : Async PeerId := do
  let k ← keyOf s
  orFail "peer id" ((do PeerId.ofPubKey (← k.toPublic) : Except Libp2p.Identity.Error PeerId)
    |>.mapError fun e => (repr e).pretty)

/-- Our TLS configuration: the seed's host key, a fresh certificate key,
as in production. -/
def tlsConfig : Async Tls.Config := do
  orFail "tls config" ((← Tls.Config.generate (← keyOf leanSeed)).mapError fun e => (repr e).pretty)

/-- Our agent version in identify. The go side checks it. -/
def leanAgent : String := "leanp2p-interop"

/-- Serve identify on `h`: our listen addresses, the ids of `handlers`
and of identify itself, and `leanAgent`. -/
def serveIdentify (h : Host) (listenAddrs : List Multiformats.Multiaddr)
    (handlers : List StreamHandler) : Async Unit := do
  let protocols := (handlers.map (·.id.toString)) ++ [Libp2p.Protocols.Identify.protocolId.toString]
  h.setHandler (Libp2p.Protocols.Identify.respondHandler (← pubOf leanSeed)
    (listenAddrs.map (·.toBytes)) protocols leanAgent)

/-- Read a stream to its end. -/
def readAll (s : Streams.Stream) : Async ByteArray := do
  let mut acc := ByteArray.empty
  let mut more := true
  while more do
    match ← s.read with
    | .ok (some b) => acc := acc ++ b
    | .ok none => more := false
    | .error e => fail s!"stream read: {repr e}"
  return acc

/-- Write to a stream, or fail. -/
def writeOk (s : Streams.Stream) (b : ByteArray) : Async Unit := do
  match ← s.write b with
  | .ok () => pure ()
  | .error e => fail s!"stream write: {repr e}"

/-- The echo handler: read to the end, write it back, close. -/
def echoHandler : StreamHandler where
  id := echoId
  handle _ s := do
    let mut acc := ByteArray.empty
    let mut more := true
    while more do
      match ← s.read with
      | .ok (some b) => acc := acc ++ b
      | .ok none => more := false
      | .error _ => throw (.closed "the echo stream was reset")
    match ← s.write acc with
    | .ok () => s.close
    | .error _ => throw (.closed "the echo write was refused")

/-- Our host over QUIC, and the cell its failures land in. -/
def mkHost (handlers : List StreamHandler) : Async (Host × OnceRef (List String)) := do
  let cfg ← tlsConfig
  let failures : OnceRef (List String) ← OnceRef.new []
  let config : Config := {
    identity := ← keyOf leanSeed
    transports := []
    securedTransports := [Libp2p.Quic.transport cfg]
    security := []
    muxers := []
    handlers
    onFailure := fun f => failures.update (· ++ [toString f.error]) }
  let h ← orFail "host" ((← (Host.new config : BaseIO _)).mapError fun e => (repr e).pretty)
  return (h, failures)

/-- Fail when the host reported a failure. -/
def noFailures (failures : OnceRef (List String)) : Async Unit := do
  let fs ← (failures.get : BaseIO (List String))
  unless fs.isEmpty do fail s!"the host reported failures: {fs}"

/-- The listener side: serve the echo, and close at `/test/done`. -/
def listenMode : Async Unit := do
  let goPeer ← peerOfSeed goSeed
  let done : Chan Bool ← Chan.new 1
  -- The host is built after the handlers, so the handler reads it from
  -- this cell.
  let host : OnceRef (Option Host) ← OnceRef.new none
  let doneHandler : StreamHandler := {
    id := doneId
    handle := fun _ s => do
      -- The session is live while its stream is: check it here, before
      -- the dialer's close ends it.
      let live ← match ← (host.get : BaseIO (Option Host)) with
        | some h => (h.connected goPeer : BaseIO Bool)
        | none => pure false
      let wrote := (← s.write "bye".toUTF8) matches .ok ()
      -- The dialer closes its host after `bye`, which ends this read,
      -- with EOF or a reset. Either is the end.
      repeat
        match ← s.read with
        | .ok (some _) => pure ()
        | _ => break
      s.close
      discard (done.trySend (live && wrote) : BaseIO Bool) }
  let (h, failures) ← mkHost [echoHandler, doneHandler]
  (host.set (some h) : BaseIO Unit)
  let a ← orFail "listen" (← h.startListening (← addr "/ip4/127.0.0.1/udp/0/quic-v1"))
  serveIdentify h [a] [echoHandler, doneHandler]
  let some port := _root_.Quic.socketAddress? a |>.map (·.port) | fail "no port"
  IO.println port
  (← IO.getStdout).flush
  -- Park: the `/test/done` handler wakes it.
  let live ← done.recv
  unless live == some true do
    fail "no session with the go peer at /test/done, or the write of bye failed"
  try h.close catch e => fail s!"close: {e}"
  noFailures failures

/-- The dialer side: dial with `/p2p`, the echo through an `na`, then
`/test/done`. -/
def dialMode (port : String) : Async Unit := do
  let goPeer ← peerOfSeed goSeed
  let (h, failures) ← mkHost []
  serveIdentify h [] []
  let p ← orFail "dial" (← h.dial (← addr s!"/ip4/127.0.0.1/udp/{port}/quic-v1/p2p/{goPeer}"))
  unless p == goPeer do fail s!"the dial proved {p}, want {goPeer}"
  -- The go host lacks the first id, answers `na`, and the negotiation
  -- lands on `/test/echo`.
  let (id, s) ← orFail "new stream" (← h.newStream goPeer [unknownId, echoId])
  unless id == echoId do fail s!"negotiated {id}, want {echoId}"
  let data := payload size
  writeOk s data
  s.close
  let got ← readAll s
  unless got == data do fail s!"the echo of {size} bytes differs, got {got.size}"
  let (_, d) ← orFail "done stream" (← h.newStream goPeer [doneId])
  let mut bye := ByteArray.empty
  while bye.size < 3 do
    match ← d.read with
    | .ok (some b) => bye := bye ++ b
    | _ => fail s!"done ended after {bye.size} bytes, want \"bye\""
  unless bye == "bye".toUTF8 do fail "done answered something other than \"bye\""
  -- Our close ends the session; the go listener sees it and closes
  -- after us.
  try h.close catch e => fail s!"close: {e}"
  noFailures failures

/-! ## The refusals

The `tls.md` "Peer Authentication" MUSTs against a go peer: go refuses
a certificate of ours that breaks them, and we refuse one of go's. Both
sides refuse inside the TLS handshake, so the refused side reads the
alert as CRYPTO_ERROR, 0x100 plus the alert (RFC 9001 §4.8). The go
side of each mode is in `scripts/quic-interop/refuse.go`. -/

/-- The TLS alert `bad_certificate` (RFC 8446 §6.2). -/
def badCertificate : UInt64 := 42

/-- The transport error of a TLS alert. -/
def alertCode (alert : UInt64) : UInt64 := 0x100 + alert

/-- A self-signed P-256 certificate with an extension of another OID in
place of the libp2p one, its key, and a window that holds now. -/
def plainCertificate : Async (ByteArray × ByteArray) := do
  let key ← orFail "cert key" ((← Crypto.p256Generate.run).mapError fun e => (repr e).pretty)
  let now ← (Tls.wallSeconds : IO Int)
  let cert ← orFail "issue" ((← (Crypto.issue key "1.3.6.1.4.1.53594.1.2" ⟨#[0, 0]⟩ false
    (now - 60) (now + 3600)).run).mapError fun e => (repr e).pretty)
  return (cert, key)

/-- The code of the peer's refusal of a raw dial. A client sends its
certificate in its last flight, so the dial may finish before the peer
refuses; the peer's alert then ends the connection's join. -/
def refusalCode (dialed : Except _root_.Quic.Error _root_.Quic.Conn) : Async UInt64 := do
  let ended ← match dialed with
    | .error e => pure (.error e)
    | .ok c => c.join
  match ended with
  | .error (.peerFailed code _) => return code
  | .error e => fail s!"the refused dial ended with {e}, want the peer's alert"
  | .ok () => fail "the peer kept a connection it must refuse"

/-- Dial the go listener with a certificate that breaks a MUST, and check
that go answers `bad_certificate`. The go listener's certificate is not
under test here, so the dial takes any. -/
def refusedDial (name : String) (ctx : _root_.Tls.Context) (a : Multiformats.Multiaddr) :
    Async Unit := do
  let code ← refusalCode (← _root_.Quic.dial ctx a (fun _ => none))
  let want := alertCode badCertificate
  unless code == want do fail s!"{name}: go ended the connection with {code}, want {want}"

/-- Two refused dials against the go host, then the dial of `dialMode`,
which also ends the go listener's run. The first refused dial carries a
certificate without the libp2p extension ("If this extension is
missing, endpoints MUST abort"). The second carries a chain of two
("Endpoints MUST abort the connection attempt if more than one
certificate is received"). -/
def dialRefusedMode (port : String) : Async Unit := do
  let a ← addr s!"/ip4/127.0.0.1/udp/{port}/quic-v1"
  let (plain, plainKey) ← plainCertificate
  let ctx ← orFail "context" (← _root_.Tls.Context.new plain plainKey Tls.alpn)
  refusedDial "no libp2p extension" ctx a
  let cfg ← tlsConfig
  unless (← (TlsNative.addChainCertificate cfg.context.native plain : IO Bool)) do
    fail "the context refused the second certificate"
  refusedDial "a chain of two" cfg.context a
  dialMode port

/-- Dial the go server of `listen-sni` through the QUIC transport, check
its peer id, and wait for the server's close. The go side checks that
our ClientHello named no server. The server closes first. Our dial ends
before our Finished leaves, so a close of ours could end the connection
inside the server's handshake (RFC 9000 §10.2.3). Go's `Accept` would
then never answer. -/
def dialHandshakeMode (port : String) : Async Unit := do
  let goPeer ← peerOfSeed goSeed
  let cfg ← tlsConfig
  let s ← orFail "dial"
    (← ((Libp2p.Quic.transport cfg).dial (← addr s!"/ip4/127.0.0.1/udp/{port}/quic-v1")
      (some goPeer) (← Chan.new 1)).run)
  unless s.remotePeer == goPeer do fail s!"the dial proved {s.remotePeer}, want {goPeer}"
  -- Park: the server's close ends the session.
  match ← s.session.join.run with
  | .ok () => pure ()
  | .error e => fail s!"the session ended with {e}, want the server's orderly close"

/-- Dial the go server of `listen-badcert`, whose certificate lacks the
libp2p extension: our check must refuse it inside the handshake, and
the go side checks the alert. -/
def dialBadCertMode (port : String) : Async Unit := do
  let cfg ← tlsConfig
  match ← ((Libp2p.Quic.transport cfg).dial (← addr s!"/ip4/127.0.0.1/udp/{port}/quic-v1")
      none (← Chan.new 1)).run with
  | .error (.authentication d) => IO.eprintln s!"lean: refused: {d}"
  | .error e => fail s!"the dial failed with {e}, want an authentication failure"
  | .ok _ => fail "the dial took a certificate without the libp2p extension"

end Tests.Interop.Quic

def main (args : List String) : IO UInt32 := do
  let run : Conc.Async Unit := match args with
    | ["listen"] => Tests.Interop.Quic.listenMode
    | ["dial", port] => Tests.Interop.Quic.dialMode port
    | ["dial-refused", port] => Tests.Interop.Quic.dialRefusedMode port
    | ["dial-handshake", port] => Tests.Interop.Quic.dialHandshakeMode port
    | ["dial-badcert", port] => Tests.Interop.Quic.dialBadCertMode port
    | _ => Tests.Interop.Quic.fail
      "usage: quic-interop listen | dial PORT | dial-refused PORT | dial-handshake PORT | dial-badcert PORT"
  try
    run.run
    IO.eprintln "lean: ok"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
