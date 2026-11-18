import Conc
import Streams
import Tls
import Quic
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Security.Tls.Constants
import Libp2p.Security.Tls.Certificate
import Libp2p.Security.Tls.Protocol
import Libp2p.Quic.Constants

/-!
# The QUIC transport value

`Libp2p.Quic.transport` fills the `SecuredTransport` seam of
`libp2p/core` with QUIC (the QUIC spec, `vendor/specs/quic/README.md`).
The QUIC engine is `net/quic`, called here as `_root_.Quic`: the
namespace of this module is `Libp2p.Quic`, and inside it a bare `Quic`
names this namespace first. The TLS side is the libp2p TLS handshake of
`libp2p/security` ("Peers authenticate each other using the TLS
handshake logic described in the libp2p TLS spec", "Peer
Authentication"): the same `Tls.Config` issues our certificate and
holds the engine context with the ALPN `libp2p`, and the same checks
decide the peer's certificate.

## The check

The engine runs the check inside the handshake (`net/quic`, "The
certificate check"). So a refused peer gets the alert `bad_certificate`
in a CONNECTION_CLOSE of CRYPTO_ERROR 0x12a (RFC 9001 §4.8). The dial
or the accept fails before the host sees the connection.

* **A dial** reads the wall clock once, before the handshake, as the
  TLS value over TCP does (`Libp2p/Security/Tls/Protocol.lean`, "The
  time"). Its check runs `Tls.verify` at that time, and it also
  compares the proved peer id with the expected one, as go-libp2p's
  `VerifyPeerCertificate` does
  (`vendor/go-libp2p/p2p/security/tls/crypto.go`, lines 143 to 149).
  The TLS spec: "Clients MUST verify that the peer ID derived from the
  certificate matches the peer ID they intended to connect to".
* **A listener** gives the engine an admission, which the engine runs
  when a connection's first datagram arrives. It asks the owner's
  `Admit` first (the seam, "The admission"): a refusal costs the peer a
  CONNECTION_REFUSED and us no handshake. An admitted connection gets
  its own check, which reads the wall clock at its own start. Its scope
  travels with it to the owner. A connection that never reaches the
  owner releases its scope. The engine releases it for a connection
  that ends in its handshake. The value releases it for a connection
  that it refuses after the handshake.

A failed read of the wall clock gives a check that refuses every
certificate: the validity window cannot be checked, and the spec says
to abort.

After the handshake, the value reads the peer with `Tls.identity`,
which runs every step of `Tls.verify` but the validity window, and
`Tls.identity_of_verify` states that the two agree. A disagreement
cannot occur; its arm closes the connection, fail-closed.

## The ALPN

QUIC requires ALPN (RFC 9001 §8.1; the QUIC spec, "ALPN": "QUIC
enforces the use of ALPN, so the handshake will fail if both peers
can't agree on the application protocol"). The engine closes a
connection that negotiated none, the context offers and selects
`libp2p` alone, and libssl refuses a selection we did not offer. So a
connection always carries `libp2p`; the value checks it again,
fail-closed.

## The streams

QUIC streams are the muxer streams (RFC 9000 §2).
`MuxSession.openStream` opens a bidirectional stream and drops the
protocol id, as yamux does. The stream's protocol comes from
multistream-select on the stream (the connections spec, "Opening New
Streams Over a Connection").
-/

set_option autoImplicit false

namespace Libp2p.Quic

open Conc Streams Multiformats Libp2p.Identity Libp2p.Core
open Libp2p.Security

/-- The seam error of an engine error. A refused certificate is
`authentication`. A transport error, ours or the peer's, is `protocol`.
A peer that refused our certificate closes with CRYPTO_ERROR, and the
TLS value over TCP reads the peer's alert as `protocol` too. A timer is
`timeout`, and the other ends are `closed`. -/
def mapError : _root_.Quic.Error → Core.Error
  | e@(.refused _) => .authentication (toString e)
  | e@(.failed _ _) | e@(.peerFailed _ _) => .protocol (toString e)
  | e@.timeout | e@.idle => .timeout (toString e)
  | e@(.closed _ _) | e@(.dropped _) | e@.ended => .closed (toString e)
  | e@.address | e@.endpoint => .protocol (toString e)

/-- A refused certificate keeps its class. -/
example : mapError (.refused "the certificate has expired") matches .authentication _ := rfl

/-- The check of a dial (the module doc, "The check"): `Tls.verify` at
`now`, and the expected peer id when there is one. -/
def dialCheck (now : Int) (expected : Option PeerId) (der : ByteArray) : Option String :=
  match Tls.verify der now, expected with
  | .error e, _ => some (toString e)
  | .ok _, none => none
  | .ok v, some want =>
    if v.peer == want then none
    else some s!"the peer proved {v.peer}, and the dialer expected {want}"

/-- The check of a time that could not be read: it refuses every
certificate (the module doc, "The check"). -/
def clockFailed (e : IO.Error) (_der : ByteArray) : Option String :=
  some s!"the validity window cannot be checked: the wall clock read failed: {e}"

/-- The muxer session over a QUIC connection. -/
private def sessionOf (c : _root_.Quic.Conn) : MuxSession where
  openStream := fun _ => ExceptT.mk ((·.mapError mapError) <$> c.openStream)
  accept := c.accept
  close := c.close _root_.Quic.orderlyClose ""
  join := ExceptT.mk ((·.mapError mapError) <$> c.join)

/-- The session of a connection whose handshake the check accepted:
the ALPN and the peer, both fail-closed (the module doc). A refusal
closes the connection, waits for its end, and answers `err`. -/
private def admit (cfg : Tls.Config) (c : _root_.Quic.Conn) (expected : Option PeerId) :
    Async (Except Core.Error SecuredSession) := do
  let refuse (err : Core.Error) : Async (Except Core.Error SecuredSession) := do
    c.close protocolViolation (toString err)
    discard c.join
    return .error err
  unless c.alpn == Tls.alpn do
    return ← refuse (.protocol s!"quic: the peer selected ALPN '{c.alpn}'")
  match Tls.identity c.peerCertificate with
  | .error e => refuse (.authentication s!"quic: {e}")
  | .ok v =>
    if let some want := expected then
      unless v.peer == want do
        return ← refuse (.authentication s!"quic: the peer proved {v.peer}, want {want}")
    return .ok {
      session := sessionOf c
      localPeer := cfg.localPeer
      remotePeer := v.peer
      localAddr := c.localAddr
      remoteAddr := c.remoteAddr }

/-- The next connection of the listener that `admit` takes, with its
scope. A refused one releases its scope. The function is `partial`: it
ends when one passes or the listener closes, and no measure bounds the
refused peers before that. -/
private partial def acceptChecked (cfg : Tls.Config)
    (l : _root_.Quic.Listener ConnectionScope) :
    Async (Option (SecuredSession × ConnectionScope)) := do
  -- Park: a peer's finished handshake wakes it, and so does the
  -- listener's close.
  match ← l.accept with
  | none => return none
  | some (c, scope) =>
    match ← admit cfg c none with
    | .ok s => return some (s, scope)
    | .error _ =>
      scope.release
      acceptChecked cfg l

/-- The check of a listener's connection: it reads the wall clock when
the connection's handshake starts. -/
private def listenCheck (cfg : Tls.Config) : BaseIO _root_.Quic.Check := do
  match ← (cfg.now.toBaseIO : BaseIO (Except IO.Error Int)) with
  | .ok now => return Tls.certificateCheck now
  | .error e => return clockFailed e

/-- The engine's admission of a listener's new connection (the module
doc, "The check"): the owner's `Admit`, then the connection's check,
with the scope as the engine's value. -/
private def listenAdmit (cfg : Tls.Config) (owner : Admit) (localAddr remoteAddr : Multiaddr) :
    BaseIO (Option (_root_.Quic.Admitted ConnectionScope)) := do
  let some scope ← owner localAddr remoteAddr | return none
  return some { check := ← listenCheck cfg, value := scope, release := scope.release }

/-- The QUIC transport for the TLS configuration `cfg`. The engine's
timers run on `cfg.clock`, so a test clock reaches them too (root
§3.1). -/
def transport (cfg : Tls.Config) : SecuredTransport where
  handles := _root_.Quic.handles
  dial := fun addr expected abort => ExceptT.mk do
    -- `toBaseIO` turns a failed read into a value: the check then
    -- refuses, and no exception escapes the dial.
    let check ← match ← (cfg.now.toBaseIO : BaseIO (Except IO.Error Int)) with
      | .ok now => pure (dialCheck now expected)
      | .error e => pure (clockFailed e)
    match ← _root_.Quic.dial cfg.context addr check cfg.clock (some abort) with
    | .error e => return .error (mapError e)
    | .ok c => admit cfg c expected
  listen := fun addr owner => do
    let l ← _root_.Quic.listen cfg.context addr (listenAdmit cfg owner) cfg.clock
    return {
      addr := l.addr
      accept := acceptChecked cfg l
      close := l.close
      join := l.join }

/-- The test value (§3.1): QUIC over `Tls.Config.fixed`, with a fixed
host key, a fixed certificate key, and a wall clock fixed at `now`. So
the peer ids and every validity answer repeat from run to run; the
handshake bytes still vary, as for the TLS test value. -/
def fixedKeyTransport (key : PrivKey) (certKey : ByteArray) (now : Int) :
    IO (Except Tls.ConfigError SecuredTransport) := do
  return (← Tls.Config.fixed key certKey now).map transport

end Libp2p.Quic
