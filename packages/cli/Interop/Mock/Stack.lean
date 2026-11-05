import Conc
import Streams

/-!
# Mock: the unmerged stack under the harness

The harness composes a host from `libp2p/identity` (W5.1),
`libp2p/core` (W5.2), `libp2p/security` (W5.3), `libp2p/mux` (W5.4),
`libp2p/host` (W5.6), and `libp2p/protocols` (W5.7). None has merged,
so the harness builds against mocks of their frozen surfaces (RULES.md,
"Working ahead of the tree"). The mock imports nothing from those
packages. It states no axiom.

The forms:

* A type is a copy of the frozen shape, reduced to the fields the
  harness touches. The sources: the root ARCHITECTURE §3.1 and §4.9,
  and the public surface sections of the host, security, mux, and
  protocols ARCHITECTURE files.
* An operation is `opaque`, and its body fails with the name of the
  missing package. No body fakes a connection, a handshake, or an
  identity, so the harness cannot pass a live run against this mock.

`Host.newStream` follows go-libp2p's `host.NewStream`
(`vendor/go-libp2p/core/host/host.go`, lines 61 to 65): a peer and the
protocol ids in preference order, answered with the stream and the id
it selected. The
host ARCHITECTURE, "Public surface", names no outbound stream call, and
this unit adds the line there.

At integration, the harness imports the real packages, and the module
goes.
-/

set_option autoImplicit false

namespace Interop.Mock

/-! ## `libp2p/identity` -/

/-- A peer id. The harness prints it, and puts it in a `/p2p`
component. -/
structure PeerId where
  /-- The base58 text of the multihash. -/
  text : String
  deriving DecidableEq, Repr

/-- The host identity key. -/
structure PrivKey where
  /-- The key bytes. -/
  raw : ByteArray

/-- A fresh Ed25519 identity. -/
opaque generateKey : IO PrivKey :=
  throw (IO.userError "libp2p/identity (W5.1) is not integrated")

/-! ## `libp2p/core` -/

/-- A protocol id, wrapped (root §3.4). -/
structure ProtocolId where
  /-- The id text. -/
  toString : String
  deriving DecidableEq, Repr

/-- The coarse error every seam returns (root §4.9). -/
inductive CoreError where
  | protocol (detail : String)
  | authentication (detail : String)
  | timeout (detail : String)
  | closed (detail : String)
  deriving Repr

/-- A security protocol value: its id, and its handshake (root §4.9). -/
structure SecurityProtocol where
  /-- The negotiated id. -/
  id : ProtocolId

/-- A muxer value: its id, and its session entry (root §4.9). -/
structure Muxer where
  /-- The negotiated id. -/
  id : ProtocolId

/-- A stream handler: its id, and its serve function (root §3.1). -/
structure StreamHandler where
  /-- The negotiated id. -/
  id : ProtocolId

/-! ## `libp2p/security` and `libp2p/mux` -/

/-- `Noise.securityProtocol`, for the identity `key`. -/
opaque noise (_key : PrivKey) : SecurityProtocol :=
  ⟨⟨"/noise"⟩⟩

/-- `Mux.yamux`. -/
opaque yamux : Muxer := ⟨⟨"/yamux/1.0.0"⟩⟩

/-- `Mux.mplex`. -/
opaque mplex : Muxer := ⟨⟨"/mplex/6.7.0"⟩⟩

/-! ## `libp2p/protocols` -/

namespace Ping

/-- `Ping.protocolId`. -/
opaque protocolId : ProtocolId := ⟨"/ipfs/ping/1.0.0"⟩

/-- The payload size of one ping. -/
def payloadSize : Nat := 32

/-- The ping handler, which echoes each payload. -/
opaque handler : StreamHandler := ⟨⟨"/ipfs/ping/1.0.0"⟩⟩

/-- One ping: send the payload, await the echo, check it, and answer
the round trip in milliseconds (the shape of W5.7's `Ping.ping`). -/
opaque ping (_s : Streams.Stream) (_clock : Conc.Clock) (_payload : ByteArray) :
    Conc.Async (Except String (Option Nat)) :=
  return .error "libp2p/protocols (W5.7) is not integrated"

end Ping

/-! ## `libp2p/host` -/

/-- `Host.Error`, with the arms of the host ARCHITECTURE. -/
inductive HostError where
  | upgrade (reason : CoreError)
  | gated
  | noAddresses (peer : PeerId)
  | closing
  deriving Repr

/-- The configuration of `Host.new`: the ordered seam lists and the
identity (root §3.1; the host ARCHITECTURE, "Public surface"). -/
structure HostConfig where
  /-- The identity key. -/
  key : PrivKey
  /-- The transports, in preference order. -/
  transports : List Streams.Transport
  /-- The security protocols, in preference order. -/
  securities : List SecurityProtocol
  /-- The muxers, in preference order. -/
  muxers : List Muxer
  /-- The initial handler set. -/
  handlers : List StreamHandler

/-- A running host. -/
structure Host where
  /-- The local peer id. -/
  id : PeerId

/-- Start a host. -/
opaque Host.new (_config : HostConfig) : Conc.Async (Except HostError Host) :=
  return .error (.upgrade (.closed "libp2p/host (W5.6) is not integrated"))

/-- Listen on an address. The answer is the bound address. -/
opaque Host.startListening (_h : Host) (_addr : Multiformats.Multiaddr) :
    Conc.Async (Except HostError Multiformats.Multiaddr) :=
  return .error .closing

/-- Dial an address. A trailing `/p2p/<id>` supplies the expected peer.
The answer is the peer the handshake proved. -/
opaque Host.dial (_h : Host) (_addr : Multiformats.Multiaddr) :
    Conc.Async (Except HostError PeerId) :=
  return .error .closing

/-- Open a stream to a peer, and negotiate one of the ids. -/
opaque Host.newStream (_h : Host) (_peer : PeerId) (_protocols : List ProtocolId) :
    Conc.Async (Except HostError (ProtocolId × Streams.Stream)) :=
  return .error .closing

/-- Run the shutdown sequence of root §5.5. -/
opaque Host.close (_h : Host) : Conc.Async Unit :=
  return ()

end Interop.Mock
