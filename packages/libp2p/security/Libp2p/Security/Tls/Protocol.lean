import Std.Time
import Conc
import Streams
import Tls
import Libp2p.Identity
import Libp2p.Core.Security
import Libp2p.Security.Tls.Constants
import Libp2p.Security.Tls.Certificate

/-!
# The TLS seam value

`Tls.securityProtocol` fills the `SecurityProtocol` seam of
`libp2p/core` with the libp2p TLS handshake (the TLS spec; root
ARCHITECTURE §4.9). The TLS 1.3 engine is `net/tls`, which this module
calls as `_root_.Tls`: the namespace of this module is
`Libp2p.Security.Tls`, and inside it a bare `Tls` names this namespace
first.

## The handshake

The dialer is the TLS client and the listener the TLS server, as in
go-libp2p (`vendor/go-libp2p/p2p/security/tls/transport.go`,
`SecureOutbound` runs `tls.Client`). `net/tls` enforces TLS 1.3, the
client certificate, the one-certificate chain, and the ALPN name. The
value gives the engine its check, `Tls.verify`
(`Libp2p/Security/Tls/Certificate.lean`), and the engine runs it inside
the handshake, as go-libp2p runs its check in `VerifyPeerCertificate`
(`vendor/go-libp2p/p2p/security/tls/crypto.go`, lines 119 to 154). A
refused certificate fails the handshake, the peer gets the alert
`bad_certificate`, and the answer is `Core.Error.authentication` with
the reason of the check. So no byte of the connection reaches a caller
before the check.

The client may finish before the server has checked the client's
certificate (the spec's "Note for clients"). A server that refuses
then sends its alert, and the client's first read ends.

## The muxer

The spec lets a client offer muxer ids in ALPN ("Inlined Muxer
Negotiation"). This value offers `libp2p` alone, so the muxer comes
from multistream-select after the handshake, as for Noise. go-libp2p's
server takes `libp2p` from that offer and falls back to
multistream-select too (the package ARCHITECTURE, "Decisions").

A peer that uses no ALPN at all, a client that offers none or a server
that selects none, gets the same answer: no inlined muxer. The spec
asks the server to abort only when it supports none of the offered
protocols, and the references accept a missing ALPN over TCP: Go's
`crypto/tls` and rustls under rust-libp2p in both roles, and
js-libp2p's client (the package ARCHITECTURE, "Decisions"). Go and
rustls require ALPN for QUIC alone (RFC 9001 §8.1).

## The leftover

`net/tls` feeds every byte into its engine, the bytes the negotiation
over-read included, so the engine holds the handshake's over-read
itself. `SecureConn.leftover` is empty, and `read` delivers the
decrypted bytes (root §4.7).

## The time

The validity check reads the wall clock, and the deadlines read the
monotonic `Clock` (§3.1). A certificate's times are calendar times, so
`Config.now` is a seam of its own, and a test can fix it. The value
reads it once, before the first byte of the handshake, and the check
inside the handshake uses that time. The handshake runs under the
upgrader's deadline (root §5.4), so the time read lies at most that
deadline before the certificate's arrival. A failed clock read gives
no time to check, and the spec says to abort when the check cannot
pass. So the value closes the connection before the handshake and
answers `Core.Error.authentication`.
-/

set_option autoImplicit false

namespace Libp2p.Security.Tls

open Conc Streams Libp2p.Identity Libp2p.Core

/-- The wall-clock time, in seconds since the Unix epoch. A failed read
throws; the caller decides what a missing time means. -/
def wallSeconds : IO Int := do
  return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-- What a TLS endpoint holds: the peer id of the host key, the issued
certificate, and the engine context over that certificate. The host
key itself is not kept: it signed the certificate, and the handshake
needs only the certificate key. -/
structure Config where
  /-- The peer id of the host key. -/
  localPeer : PeerId
  /-- Our certificate and its key. -/
  identity : Identity
  /-- The engine context over `identity`, with the ALPN `libp2p`. -/
  context : _root_.Tls.Context
  /-- The wall clock of the validity check (the module doc, "The
  time"). -/
  now : IO Int := wallSeconds
  /-- The monotonic clock that bounds the `close_notify` write of a
  secure connection (§3.1). A test passes the clock it advances. -/
  clock : Clock := Clock.system

/-- Why a `Config` could not be built. -/
inductive ConfigError where
  /-- The host key derives no peer id. -/
  | identity (e : Identity.Error)
  /-- Issuing the certificate failed. -/
  | certificate (e : IssueError)
  /-- The engine refused the certificate or its key. -/
  | context (e : _root_.Tls.Error)
  deriving Repr

/-- A configuration for the host key `key` on the certificate key
`certKey` (P-256, SEC1 DER), issued at the time `now` gives, which also
becomes the clock of the validity check. `Config.fixed` is the test
form. A failed read of `now` throws, as any IO failure of the setup
does. -/
def Config.ofCertKey (key : PrivKey) (certKey : ByteArray) (now : IO Int := wallSeconds) :
    IO (Except ConfigError Config) := do
  match (key.toPublic.bind PeerId.ofPubKey) with
  | .error e => return .error (.identity e)
  | .ok localPeer =>
    match ← (Identity.issue key certKey (← now)).run with
    | .error e => return .error (.certificate e)
    | .ok identity =>
      match ← _root_.Tls.Context.new identity.certificate identity.certificateKey alpn with
      | .error e => return .error (.context e)
      | .ok context => return .ok { localPeer, identity, context, now }

/-- A configuration for the host key `key` on a fresh certificate key. -/
def Config.generate (key : PrivKey) : IO (Except ConfigError Config) := do
  match ← Crypto.p256Generate.run with
  | .error e => return .error (.certificate (.backend e))
  | .ok certKey => Config.ofCertKey key certKey

/-- The seam error of an engine failure. A refused certificate is
`authentication`: the engine refused it (a chain of more than one, no
client certificate), or `verify` did inside the handshake, and the
text then names the check that failed. A close during the handshake is
`closed`; the rest is `protocol`. -/
private def mapEngineError : _root_.Tls.Error → Core.Error
  | .closed => .closed "tls: the peer closed the connection during the handshake"
  | e@(.peerCertificate _) => .authentication (toString e)
  | e => .protocol (toString e)

/-- The check the engine runs on the peer's certificate (`net/tls`,
"The certificate check"): `verify` at the time `now`, `none` to accept
and the text of the `CertError` to refuse. It is pure, so the shim can
call it with no `IO` convention, and the same certificate and time give
the same answer after the handshake. -/
def certificateCheck (now : Int) (der : ByteArray) : Option String :=
  match verify der now with
  | .ok _ => none
  | .error e => some (toString e)

/-- The handshake at the time `now` of the validity check (the module
doc, "The handshake"). -/
private def handshakeAt (cfg : Config) (now : Int) (role : Role) (conn : Connection)
    (leftover : ByteArray) : Async (Except Core.Error SecureConn) := do
  match ← _root_.Tls.handshake cfg.context (role == .responder) conn leftover
      (certificateCheck now) cfg.clock with
  | .error e =>
    conn.closeQuietly
    return .error (mapEngineError e)
  | .ok sec =>
    -- A fatal error after the handshake: close with no alert (RFC 8446
    -- §6.2), join, and answer `err`.
    let refuse (err : Core.Error) : Async (Except Core.Error SecureConn) := do
      sec.abort
      discard sec.join
      return .error err
    -- The selected ALPN is `libp2p`, or none when the peer did not use
    -- ALPN, which reads as `libp2p` (the module doc, "The muxer"). libssl
    -- refuses an unoffered protocol on the client, and the server
    -- selects `libp2p` alone, so another value is a fault; it refuses,
    -- fail-closed.
    unless sec.alpn == alpn || sec.alpn.isEmpty do
      return ← refuse (.protocol s!"tls: the peer selected ALPN '{sec.alpn}'")
    -- The engine finished, so `certificateCheck now` accepted this
    -- certificate, and `verify` at the same time gives the same answer:
    -- the peer it proves. The error arm is a fault; it refuses,
    -- fail-closed.
    match verify sec.peerCertificate now with
    | .ok v =>
      return .ok {
        toConnection := sec.connection
        localPeer := cfg.localPeer
        remotePeer := v.peer
        leftover := .empty
        join := ExceptT.mk do
          return (← sec.join).mapError fun e => .protocol (toString e) }
    | .error e => refuse (.authentication s!"tls: {e}")

/-- The handshake of the seam: read the time of the validity check
once, before the first byte (the module doc, "The time"), then run
`handshakeAt`. `toBaseIO` turns a failed read into a value, so the
refusal closes the connection instead of an exception leaking it. -/
private def handshake (cfg : Config) (role : Role) (conn : Connection) (leftover : ByteArray) :
    ExceptT Core.Error Async SecureConn := ExceptT.mk do
  match ← (cfg.now.toBaseIO : BaseIO (Except IO.Error Int)) with
  | .ok now => handshakeAt cfg now role conn leftover
  | .error e =>
    conn.closeQuietly
    return .error (.authentication
      s!"tls: the validity window cannot be checked: the wall clock read failed: {e}")

/-- The production value: the libp2p TLS security protocol,
`/tls/1.0.0`, for `cfg`. -/
def securityProtocol (cfg : Config) : SecurityProtocol where
  id := protocolId
  handshake := handshake cfg

/-- A configuration with nothing drawn: the host key `key`, the
certificate key `certKey` (P-256, SEC1 DER), and a clock fixed at `now`
for the issue and for every validity check. So the peer id, the
certificate key, and every validity answer repeat from run to run. -/
def Config.fixed (key : PrivKey) (certKey : ByteArray) (now : Int) :
    IO (Except ConfigError Config) :=
  Config.ofCertKey key certKey (pure now)

/-- The test value (§3.1): `/tls/1.0.0` with fixed keys and a fixed
clock (`Config.fixed`). libssl draws the handshake randomness, and the
backend draws the certificate's serial number and its ECDSA nonce, so
the bytes on the wire still vary. The keys and the peer ids do not,
and that is what a suite above the transport depends on. -/
def fixedKeyProtocol (key : PrivKey) (certKey : ByteArray) (now : Int) :
    IO (Except ConfigError SecurityProtocol) := do
  return (← Config.fixed key certKey now).map securityProtocol

end Libp2p.Security.Tls
