import Conc
import Streams
import Libp2p.Identity
import Libp2p.Core.ProtocolId
import Libp2p.Core.Error
import Libp2p.Core.Role

/-!
# The security seam

After the transport hands over a raw `Connection`, the upgrader
negotiates a security protocol with multistream-select and runs its
handshake (ARCHITECTURE §4.9; the connections spec, "Upgrading
Connections"). The handshake authenticates the peer, and the result
is a `SecureConn`: a connection whose bytes travel encrypted, plus
the two peer ids the handshake proved.

`SecurityProtocol` is the seam (§3.1). Noise fills it in
`libp2p/security`, with a fixed-key test value beside it. The upgrader
imports this module and no implementation, so a new security protocol
lands as a new value (§9, delta 10).

## The monad

Every operation that can park runs in `Conc.Async` (ARCHITECTURE §4.1).
`ExceptT Error Async α` unfolds to `Async (Except Error α)`,
so a protocol failure is a value and a socket fault stays an
`IO.Error` underneath (§3.5).

## The leftover hand-over

multistream-select can read past its last message. The bytes it
over-read belong to the handshake, so the handshake takes them as its
`ByteArray` argument and consumes them before it reads the connection
(§4.7). The handshake can over-read too: transport frames that arrived
behind its last message. Those bytes are ciphertext, and they belong
to the secure transport's reader, the reader at the same level
(§4.7). The `SecureConn` records them in `leftover`, so the types show
the hand-over, and its `read` delivers them, decrypted, before any
connection byte. No stage above `read` takes the field: the muxer
stage takes plaintext through `read` and the bytes that its own
negotiation over-read.
-/

set_option autoImplicit false

namespace Libp2p.Core

open Conc Streams Libp2p.Identity

/-- A connection after a security handshake.

`extends Connection` puts the `Connection` fields first, so a
`SecureConn` is a connection with more fields, and `sc.toConnection`
is the plain connection a muxer runs over. Here `read`, `write`, and
`close` are the secure surface: `read` answers plaintext, and `write`
encrypts. The addresses are those of the underlying connection.

**Failures.** A frame that fails authentication is a protocol error
(§4.9), and the `Connection.read` type has no protocol channel. The
secure read tears the connection down first, then answers `none`, so
the layer above sees an orderly end (the security pair, contract 1).
The protocol error reaches the owner through `join` (§3.5: the owner
never learns of a failure by reading EOF). -/
structure SecureConn extends Connection where
  /-- The peer id of our identity key, the one the handshake proved to
  the peer. -/
  localPeer : PeerId
  /-- The peer id the peer proved in the handshake. The upgrader
  compares it with the expected id before the muxer stage (§4.9). -/
  remotePeer : PeerId
  /-- The ciphertext the handshake read past its last message, as a
  record of the hand-over (§4.7). These bytes seed the reader of the
  next stage, the secure transport, and `read` delivers them,
  decrypted, before any connection byte.

  No stage above `read` takes this field. The muxer stage reads
  plaintext through `read`, and its `ByteArray` argument is what the
  muxer negotiation read past its own last message. A stage that took
  this field would see ciphertext, and it would see the same frame a
  second time through `read`. -/
  leftover : ByteArray
  /-- Wait until the secure connection has ended, and answer how it
  ended: `.ok` for an orderly close, the protocol error otherwise. The
  owner calls it after `close` (§3.1, "Lifecycle"; §4.1, rule 2). -/
  join : ExceptT Error Async Unit

/-- The security seam: one security protocol that multistream-select
can negotiate. -/
structure SecurityProtocol where
  /-- The id that multistream-select negotiates, such as `/noise`. -/
  id : ProtocolId
  /-- Run the handshake in the given role over the connection. The
  `ByteArray` holds the bytes the negotiation over-read, and the
  handshake consumes them before it reads the connection (§4.7).
  The implementation maps its own error into `Error` here, once
  (owned contract 6). The deadline of §5.4 belongs to the caller. -/
  handshake : Role → Connection → ByteArray → ExceptT Error Async SecureConn

end Libp2p.Core
