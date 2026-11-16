import Streams
import Crypto
import Tls
import Libp2p.Core
import Libp2p.Security

/-!
# The TLS interop driver (unit W5.11)

The Lean side of the TLS interop check against go-libp2p v0.50.0's TLS
transport (`p2p/security/tls`, Go's `crypto/tls` under it).
`scripts/tls-interop.sh` builds the go side (`scripts/tls-interop/`)
and runs both directions over loopback TCP, with no
multistream-select, so the check sees the handshake, the certificate
checks of both sides, and the records alone.

* `tls-interop listen`: listen, print the port, accept one connection
  as the server, read `size` bytes, echo them, and then read the peer's
  orderly end.
* `tls-interop dial PORT`: connect as the client, write `size` bytes,
  check the echo, and close.
* `tls-interop listen-noext`, `tls-interop listen-chain`, and
  `tls-interop listen-nocert`: listen, and pass when the handshake
  refuses the peer with `Core.Error.authentication` for a missing
  extension, for a chain of two certificates, or for a client that sent
  no certificate (libssl's reason, "peer did not return a
  certificate").
* `tls-interop dial-refuse PORT`: connect, and pass when the handshake
  refuses an expired server certificate.
* `tls-interop dial-noext PORT`: connect through the engine with a
  certificate that lacks the libp2p extension, and pass when the
  server's alert `bad_certificate` ends the first read.

`scripts/tls-interop.sh` pairs these with the refusal, no-ALPN, and
no-SNI modes of the go side (`scripts/tls-interop/refuse.go`); the
plain `listen` and `dial` serve the no-ALPN and no-SNI runs.

The go transport offers yamux in ALPN before `libp2p`, as it does in
production. This side offers and selects `libp2p` alone, so the go
side's check that no inlined muxer was chosen covers the server's
selection and the client's offer.

Both sides take fixed Ed25519 identities from 32-byte seeds, so each
side checks the peer id the other proves. The certificate key comes
from `Config.generate`, as in production.

The driver lives outside `lake test`, which stays hermetic: Go tooling
is test-only and confined to the harness (CLAUDE.md, "Dependencies").
The payload pattern matches the go side.
-/

set_option autoImplicit false

namespace Tests.Interop.Tls

open Conc (Async)
open Libp2p.Identity
open Libp2p.Security

/-- 32 bytes of one value, the form of both identity seeds. -/
def seed (v : UInt8) : ByteArray := ⟨Array.replicate 32 v⟩

/-- Our identity seed: 32 bytes of `L`. The go side holds the same. -/
def leanSeed : ByteArray := seed 'L'.toNat.toUInt8

/-- The go side's identity seed: 32 bytes of `G`. -/
def goSeed : ByteArray := seed 'G'.toNat.toUInt8

/-- The bytes each way: past twelve TLS records of 16 KiB. -/
def size : Nat := 200000

/-- The pattern both sides build. -/
def payload (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun k => UInt8.ofNat ((k * 7 + 3) % 251)⟩

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

/-- Our seam value, and the peer id the go side must prove. -/
def setup : Async (Libp2p.Core.SecurityProtocol × PeerId) := do
  let cfg ← orFail "tls config"
    ((← Tls.Config.generate (← keyOf leanSeed)).mapError fun e => (repr e).pretty)
  let goKey ← keyOf goSeed
  let want ← orFail "go peer id"
    ((do PeerId.ofPubKey (← goKey.toPublic) : Except Error PeerId) |>.mapError fun e => (repr e).pretty)
  return (Tls.securityProtocol cfg, want)

/-- Read until `n` bytes have arrived, or the end. -/
def readN (sc : Libp2p.Core.SecureConn) (n : Nat) : Async ByteArray := do
  let mut acc := ByteArray.empty
  while acc.size < n do
    match ← sc.read with
    | some b => acc := acc ++ b
    | none => break
  return acc

/-- The secure connection's answer, as a failure when it is an error. -/
def joinOk (sc : Libp2p.Core.SecureConn) : Async Unit := do
  orFail "join" (← sc.join.run)

/-- The listener side: the server, then the echo, then the peer's
orderly end. -/
def listenMode : Async Unit := do
  let (proto, want) ← setup
  let l ← Streams.Tcp.transport.listen (← addr "/ip4/127.0.0.1/tcp/0")
  let some port := Streams.Tcp.socketAddress? l.addr |>.map (·.port) | fail "no port"
  IO.println port
  (← IO.getStdout).flush
  let some conn ← l.accept | fail "accept failed"
  l.close
  let sc ← orFail "handshake" (← (proto.handshake .responder conn .empty).run)
  unless sc.remotePeer == want do fail s!"remote peer {sc.remotePeer}, want {want}"
  let got ← readN sc size
  unless got.size == size do fail s!"read {got.size} bytes, want {size}"
  sc.write got
  -- The dialer closes after it has read the echo: an orderly end.
  if (← sc.read).isSome then fail "bytes after the echo, want the end"
  sc.close
  joinOk sc
  l.join

/-- The dialer side: the client, then the write and the echo. -/
def dialMode (port : String) : Async Unit := do
  let (proto, want) ← setup
  let some conn ← Streams.Tcp.transport.dial (← addr s!"/ip4/127.0.0.1/tcp/{port}") | fail "dial failed"
  let sc ← orFail "handshake" (← (proto.handshake .initiator conn .empty).run)
  unless sc.remotePeer == want do fail s!"remote peer {sc.remotePeer}, want {want}"
  let data := payload size
  sc.write data
  let got ← readN sc size
  unless got == data do fail s!"the echo of {size} bytes differs, got {got.size}"
  sc.close
  joinOk sc

/-- True when `text` holds `part`. -/
def mentions (text part : String) : Bool := (text.splitOn part).length > 1

/-- The listener side of a refusal: the handshake must answer
`authentication`, the class of a refused certificate, for the reason
`reason`. -/
def listenRefuseMode (reason : String) : Async Unit := do
  let (proto, _) ← setup
  let l ← Streams.Tcp.transport.listen (← addr "/ip4/127.0.0.1/tcp/0")
  let some port := Streams.Tcp.socketAddress? l.addr |>.map (·.port) | fail "no port"
  IO.println port
  (← IO.getStdout).flush
  let some conn ← l.accept | fail "accept failed"
  l.close
  match ← (proto.handshake .responder conn .empty).run with
  | .error (.authentication d) =>
    unless mentions d reason do fail s!"refused with {d}, want {reason}"
    IO.eprintln s!"lean: refused: {d}"
  | .error e => fail s!"the handshake failed with {e}, want an authentication refusal"
  | .ok sc =>
    sc.close
    discard sc.join.run
    fail "the handshake accepted the peer"
  l.join

/-- The dialer side of a refusal: an expired server certificate. -/
def dialRefuseMode (port : String) : Async Unit := do
  let (proto, _) ← setup
  let some conn ← Streams.Tcp.transport.dial (← addr s!"/ip4/127.0.0.1/tcp/{port}") | fail "dial failed"
  match ← (proto.handshake .initiator conn .empty).run with
  | .error (.authentication d) =>
    unless mentions d "expired" do fail s!"refused with {d}, want an expired certificate"
    IO.eprintln s!"lean: refused: {d}"
  | .error e => fail s!"the handshake failed with {e}, want an authentication refusal"
  | .ok sc =>
    sc.close
    discard sc.join.run
    fail "the handshake accepted an expired certificate"

/-- A client whose certificate lacks the libp2p extension, through the
engine: its handshake finishes before the server checks the
certificate (the TLS spec's "Note for clients"), and the server's alert
`bad_certificate` then ends the first read. -/
def dialNoExtMode (port : String) : Async Unit := do
  let some conn ← Streams.Tcp.transport.dial (← addr s!"/ip4/127.0.0.1/tcp/{port}") | fail "dial failed"
  let certKey ← orFail "cert key" ((← Crypto.p256Generate.run).mapError fun e => (repr e).pretty)
  let now ← Libp2p.Security.Tls.wallSeconds
  let cert ← orFail "issue" ((← (Crypto.issue certKey "1.3.6.1.4.1.53594.1.2" ⟨#[4, 0]⟩ false
    (now - 60) (now + 3600)).run).mapError fun e => (repr e).pretty)
  let ctx ← orFail "context" (← _root_.Tls.Context.new cert certKey Libp2p.Security.Tls.alpn)
  let sec ← orFail "engine handshake" (← _root_.Tls.handshake ctx false conn .empty (fun _ => none))
  if (← sec.connection.read).isSome then fail "bytes from a server that must refuse"
  sec.connection.close
  match ← sec.join with
  | .error e =>
    unless mentions (toString e) "alert bad certificate" do
      fail s!"the connection ended with {e}, want the alert bad certificate"
    IO.eprintln s!"lean: refused by the server: {e}"
  | .ok () => fail "an orderly end, want the alert bad certificate"

end Tests.Interop.Tls

def main (args : List String) : IO UInt32 := do
  let run : Conc.Async Unit := match args with
    | ["listen"] => Tests.Interop.Tls.listenMode
    | ["dial", port] => Tests.Interop.Tls.dialMode port
    | ["listen-noext"] => Tests.Interop.Tls.listenRefuseMode "lacks the libp2p extension"
    | ["listen-chain"] => Tests.Interop.Tls.listenRefuseMode "sent 2 certificates"
    | ["listen-nocert"] =>
      Tests.Interop.Tls.listenRefuseMode "peer did not return a certificate"
    | ["dial-refuse", port] => Tests.Interop.Tls.dialRefuseMode port
    | ["dial-noext", port] => Tests.Interop.Tls.dialNoExtMode port
    | _ => Tests.Interop.Tls.fail
      ("usage: tls-interop listen | dial PORT | listen-noext | listen-chain | " ++
        "listen-nocert | dial-refuse PORT | dial-noext PORT")
  try
    run.run
    IO.eprintln "lean: ok"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
