import Crypto
import Streams
import Libp2p.Identity
import Libp2p.Security.Mock.Core
import Libp2p.Security.Constants
import Libp2p.Security.Handshake
import Libp2p.Security.Payload
import Libp2p.Security.Transport

/-!
# The Noise seam values

`securityProtocol` fills the `SecurityProtocol` seam of `libp2p/core`
with Noise XX (root ARCHITECTURE §4.9), and `fixedKeyProtocol` is the
test value beside it (§3.1). Both run one handshake shell over the core
of `Libp2p.Security.Handshake`, and they differ only in the `Rng` the
shell draws the ephemeral key from.

## The handshake shell

The shell builds our payload once, through `Noise.build` and the sign
dispatch of `libp2p/identity`. It posts the entropy and the payloads as
events, and reads each peer message through the `u16be` framed reader
of `Streams.Framing`, capped at `maxMessage` (owned contract 8). The
reader starts from the bytes the negotiation over-read (owned contract
5). The shell performs the actions in order, and checks each payload
that carries the peer's static key with `Noise.verify` before the next
action. So on the initiator a bad payload of message 1 ends the
handshake before message 2 reaches the wire, as go and js order it.

The noise-libp2p spec puts the libp2p payload in the second and third
messages ("XX": "The second and third handshake messages include a
handshake payload"), so the initiator posts an empty payload for
message 0. The initiator's own payload goes in message 2, and the
responder's in message 1. The responder does not check what message 0
carries. go-libp2p, js-libp2p, and nim-libp2p drop it the same way;
rust-libp2p refuses a payload that decodes to any field (the package
ARCHITECTURE, "The responder drops the payload of message 0").

## The end of the handshake

The bytes the framed reader holds past the last message are transport
ciphertext. They seed the transport (`Transport.Session.new`), and the
`SecureConn` records them in `leftover`. A failed handshake closes the
connection, and the error reaches the caller mapped into `Core.Error`
(`Error.toCore`, owned contract 6 of `libp2p/core`).

## The static key

The Noise static key belongs to the seam value, so all handshakes of a
host share it. `Config.generate` draws it
from `Rng.system`; the test value takes a fixed one.
-/

set_option autoImplicit false

namespace Libp2p.Security.Noise

-- The seam types come from the mock of W5.2 (RULES.md, "Working ahead
-- of the tree"). At the integration, `Mock.Core` reads `Libp2p.Core`
-- again.
open Libp2p.Identity
open Conc (Async)
open Streams (Connection BufReader)

/-- The seam error of a Noise error (root §3.5). Every failure of
`Noise.verify` is a failure of the static-key check, and owned contract
4 maps it to `authentication`: the spec's check decodes the identity key
and then validates the signature ("peers MUST decode the public key …
The key MUST then be used to validate"), and `verify` gates and decodes
the payload on the way. The end of the connection inside the handshake
is `closed`; every other failure breaks the spec, and is `protocol`.
The detail is the rendered Noise error. -/
def Error.toCore (e : Error) : Mock.Core.Error :=
  let detail := s!"noise: {repr e}"
  match e with
  | .payloadTooLarge _ | .payload _ | .missingIdentity | .identity _ | .badSignature =>
    .authentication detail
  | .closed => .closed detail
  | _ => .protocol detail

/-- What a Noise seam value holds: the identity key, which signs the
payload, and the Noise static private key. -/
structure Config where
  /-- The identity key of the host. -/
  identity : PrivKey
  /-- The X25519 static private key of the handshakes. -/
  static : Bytes32

/-- 32 bytes from the `Rng`, as a key. -/
private def draw32 (rng : Crypto.Rng) : ExceptT Error IO Bytes32 := do
  let b ← (rng.bytes 32).adapt .crypto
  let some k := Bytes32.ofByteArray? b | throw (.crypto .fault)
  return k

/-- A configuration with a fresh static key from `Rng.system`. -/
def Config.generate (identity : PrivKey) : ExceptT Error IO Config := do
  return { identity, static := ← draw32 Crypto.Rng.system }

/-- An `ExceptT Error IO` step inside the shell. `Async` lifts `IO`, so
the bind inside the `do` block takes the step as it is. -/
private def ofIO {α : Type} (x : ExceptT Error IO α) : ExceptT Error Async α :=
  ExceptT.mk do return (← x.run)

/-- An `Except Error` result inside the shell. -/
private def ofExcept {α : Type} (x : Except Error α) : ExceptT Error Async α :=
  ExceptT.mk (pure x)

/-- What the shell has learned so far: the checked payload, and the
completion. -/
private structure Learned where
  verified : Option Verified := none
  completion : Option Completion := none

/-- Perform the actions of one step, in order. A payload that carries
the peer's static key is checked before the next action. -/
private def performAll (conn : Connection) (l : Learned) (acts : List Action) :
    ExceptT Error Async Learned := do
  let mut l := l
  for a in acts do
    match a with
    | .write f => conn.write f.bytes
    | .payload p (some k) => l := { l with verified := some (← ofExcept (verify k p.bytes)) }
    -- Message 0 carries no libp2p payload (module doc).
    | .payload _ none => pure ()
    | .complete c => l := { l with completion := some c }
  return l

/-- The handshake shell. The answer holds the completion, the checked
payload, and the reader that holds the bytes past the last message. -/
private def runHandshake (cfg : Config) (rng : Crypto.Rng) (role : Mock.Core.Role)
    (conn : Connection) (leftover : ByteArray) :
    ExceptT Error Async (Completion × Verified × BufReader) := do
  let st0 ← ofExcept (State.init role .empty cfg.static)
  let sPub ← ofExcept ((Crypto.x25519PublicKey cfg.static.key).mapError .crypto)
  let payload ← ofIO (build cfg.identity ⟨sPub⟩)
  let e ← ofIO (draw32 rng)
  -- The local events: the entropy, then the payload of each message we
  -- write (module doc).
  let locals : List Event := match role with
    | .initiator => [.entropy e, .«local» ⟨.empty⟩, .«local» ⟨payload⟩]
    | .responder => [.entropy e, .«local» ⟨payload⟩]
  let mut st := st0
  let mut l : Learned := {}
  for ev in locals do
    let (st', acts) ← ofExcept (step st ev)
    st := st'
    l ← performAll conn l acts
  -- The peer's messages. XX reads one on the initiator and two on the
  -- responder; the core refuses any other order.
  let mut r := BufReader.new conn leftover
  while l.completion.isNone do
    -- Park: the peer's bytes wake the read, and so does the close of the
    -- connection by the deadline of the caller (owned contract 7).
    match ← Streams.Framing.read r .u16be maxMessage with
    | .ok (some (msg, r')) =>
      r := r'
      let (st', acts) ← ofExcept (step st (.bytes ⟨msg⟩))
      st := st'
      l ← performAll conn l acts
    | .ok none => throw .closed
    -- Unreachable: `maxMessage` is the largest length two bytes carry, so
    -- no header is over the cap, and the IO read never answers
    -- `truncated` (`Streams.Framing.read`). Reaching the arm means that
    -- assumption broke, which is a fault of ours, not a protocol
    -- condition (root §3.5).
    | .error e =>
      ofIO (ExceptT.lift (throw (IO.userError
        s!"noise: Framing.read failed on a u16be prefix at cap {maxMessage}: {repr e}")))
  let some c := l.completion | throw .closed
  -- Each role reads one message that carries the peer's static key.
  let some v := l.verified | throw .missingIdentity
  return (c, v, r)

/-- The handshake of a seam value: the shell, then the transport over
the cipher states. A failure closes the connection before the answer
(root §3.5). -/
private def handshakeWith (cfg : Config) (rng : Crypto.Rng) (role : Mock.Core.Role)
    (conn : Connection) (leftover : ByteArray) : ExceptT Mock.Core.Error Async Mock.Core.SecureConn :=
  ExceptT.mk do
    let shaken ← try (runHandshake cfg rng role conn leftover).run
      catch e => do conn.closeQuietly; throw e
    match shaken with
    | .error e =>
      conn.closeQuietly
      return .error e.toCore
    | .ok (c, v, r) =>
      let localPeer ← match cfg.identity.toPublic.bind PeerId.ofPubKey with
        | .ok p => pure p
        | .error e =>
          conn.closeQuietly
          return .error (Error.identity e).toCore
      let s ← Transport.Session.new conn c r.leftover
      return .ok {
        read := s.read
        write := s.write
        close := s.close
        localAddr := conn.localAddr
        remoteAddr := conn.remoteAddr
        localPeer
        remotePeer := v.peer
        leftover := r.leftover
        join := ExceptT.mk do return (← s.join).mapError Error.toCore }

/-- The production value: Noise with the configured keys, and the
ephemeral keys from `Rng.system`. -/
def securityProtocol (cfg : Config) : Mock.Core.SecurityProtocol where
  id := protocolId
  handshake := handshakeWith cfg Crypto.Rng.system

/-- The test value (§3.1): Noise with fixed keys. Each handshake draws
its ephemeral key from a fresh `Rng.seeded seed`, so with an Ed25519
identity, whose signature is deterministic (§3.6), the same peer
behavior gives the same bytes on the wire. -/
def fixedKeyProtocol (cfg : Config) (seed : ByteArray) : Mock.Core.SecurityProtocol where
  id := protocolId
  handshake role conn leftover := ExceptT.mk do
    let rng ← Crypto.Rng.seeded seed
    (handshakeWith cfg rng role conn leftover).run

end Libp2p.Security.Noise
