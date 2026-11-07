import Conc
import Streams
import Bytes

/-!
# Unmerged node dependencies

W5.8 consumes the identity, core, host, security, mux and protocol
surfaces. Their implementations are still open. This module supplies
their names under `Mock`, as RULES permits. Opaque operations have
executable failure bodies. They never simulate a successful network
connection, derive a fake identity, or add an axiom.

The narrow address and peer representations serve CLI workflow tests.
They make no claim about address validation or cryptography. Replace
them with the real types at integration. The package plan lists every
connection, including the host API refinements that still need review.
-/

set_option autoImplicit false

namespace CliApp.Mock

/-- The CLI only inspects whether the final component names a peer. -/
inductive Protocol where
  | p2p | other
  deriving BEq, DecidableEq, Repr

/-- The component shape matches the multiaddr accessor used at integration. -/
structure Component where
  proto : Protocol
  value : List Nat
  deriving BEq, DecidableEq, Repr

/-- The address text boundary belongs to multiformats. -/
structure Multiaddr where
  text : String
  components : List Component
  deriving BEq, DecidableEq, Repr

namespace Multiaddr

/-- Mock segmentation rejects empty text; value validation belongs to W2.3. -/
opaque parse? (text : String) : Except String Multiaddr :=
  if text.startsWith "/" && text != "/" && !((text.splitOn "/").drop 1).contains "" then
    let parts := text.splitOn "/"
    let namedPeer := (parts.dropLast.getLast? == some "p2p" ||
      parts.dropLast.getLast? == some "ipfs") && !parts.contains "unix"
    .ok ⟨text, [⟨if namedPeer then .p2p else .other, []⟩]⟩
  else .error "invalid multiaddr"

/-- The display accessor matches the canonical address boundary. -/
opaque toString (address : Multiaddr) : String := address.text

end Multiaddr

/-- Peer identity is opaque to the CLI, which only prints or compares it. -/
structure PeerId where
  text : String
  deriving BEq, DecidableEq, Repr

/-- Peer-id presentation belongs to identity. -/
opaque PeerId.toBase58 (peer : PeerId) : String := peer.text

/-- Key data stays in the identity package at the real boundary. -/
structure PrivKey where
  raw : ByteArray

/-- The public key is supplied by identity, never derived in a binary. -/
structure PubKey where
  raw : ByteArray

/-- A fixed-size secret crosses the crypto boundary with its size proof. -/
structure Key32 where
  bytes : ByteArray
  sizeEq : bytes.size = 32

/-- Negotiation compares wrapped ids. Literal names remain with their protocols. -/
structure ProtocolId where
  toString : String
  deriving BEq, DecidableEq, Repr

/-- The coarse errors that the host wraps once. -/
inductive CoreError where
  | protocol (detail : String)
  | authentication (detail : String)
  | timeout (detail : String)
  | closed (detail : String)
  deriving BEq, DecidableEq, Repr

/-- The binary acts on the host error channel alone. -/
inductive HostError where
  | upgrade (reason : CoreError)
  | gated
  | noAddresses (peer : PeerId)
  | closing
  deriving BEq, DecidableEq, Repr

/-- Explicit failure from an unmerged operation. -/
def unavailable (package : String) : HostError :=
  .upgrade (.closed s!"{package} is not integrated; network commands are unavailable")

/-- The direction that security and muxer implementations consume. -/
inductive Role where
  | initiator | responder

/-- The security result retains the previous stage's leftover bytes. -/
structure SecureConn where
  connection : Streams.Connection
  localPeer : PeerId
  remotePeer : PeerId
  leftover : ByteArray
  close : IO Unit
  join : Conc.Async Unit

/-- The frozen security seam; the CLI assembles values, never handshake code. -/
structure SecurityProtocol where
  id : ProtocolId
  handshake : Role → Streams.Connection → ByteArray → ExceptT CoreError Conc.Async SecureConn

/-- The mux session owns its close and its completion. -/
structure MuxSession where
  openStream : ExceptT CoreError Conc.Async Streams.Stream
  accept : Conc.Async (Option Streams.Stream)
  close : IO Unit
  join : Conc.Async Unit

/-- The frozen muxer seam with a single direction-sensitive entry point. -/
structure Muxer where
  id : ProtocolId
  «open» : Role → Streams.Connection → ByteArray → ExceptT CoreError Conc.Async MuxSession

/-- The host dispatches one handler per wrapped protocol id. -/
structure StreamHandler where
  id : ProtocolId
  handle : Streams.Stream → ExceptT CoreError Conc.Async Unit

/-- Policy decisions remain runtime values, as in the frozen core seam. -/
inductive Decision where
  | allow | deny

/-- The gater is selected by configuration, never hard-coded in the host. -/
structure ConnectionGater where
  allowDial : PeerId → Multiaddr → BaseIO Decision
  allowAccept : Multiaddr → BaseIO Decision
  allowSecured : Role → PeerId → BaseIO Decision

/-- Memory and lifecycle hooks of one resource scope. -/
structure ResourceScope where
  reserveMemory : Nat → BaseIO Decision
  releaseMemory : Nat → BaseIO Unit
  close : BaseIO Unit

/-- Stream scopes belong to their connection's grant. -/
structure ConnectionScope extends ResourceScope where
  setPeer : PeerId → BaseIO Decision
  openStream : Role → BaseIO (Option ResourceScope)

/-- Resource policy is supplied alongside the transport and protocol choices. -/
structure ResourceManager where
  openConnection : Role → Multiaddr → BaseIO (Option ConnectionScope)

/-- Ranking changes order while preserving every address. -/
structure AddressRanker where
  rank : PeerId → List Multiaddr → List Multiaddr
  rank_perm : ∀ peer addresses, (rank peer addresses).Perm addresses

namespace Policy

/-- Permissive policy is a host-owned dependency value. -/
opaque permissiveGater : ConnectionGater :=
  { allowDial := fun _ _ => pure .allow
    allowAccept := fun _ => pure .allow
    allowSecured := fun _ _ => pure .allow }

/-- W5.6 defers limiting policy implementations behind the same seam. -/
opaque unlimitedResources : ResourceManager :=
  { openConnection := fun _ _ => pure (some {
      reserveMemory := fun _ => pure .allow
      releaseMemory := fun _ => pure ()
      close := pure ()
      setPeer := fun _ => pure .allow
      openStream := fun _ => pure (some {
        reserveMemory := fun _ => pure .allow
        releaseMemory := fun _ => pure ()
        close := pure () }) }) }

/-- The default ranker preserves the caller's order. -/
opaque identityRanker : AddressRanker := ⟨fun _ addresses => addresses, fun _ _ => .refl _⟩

end Policy

/-- Configuration is the composition statement, with ordered implementation lists. -/
structure HostConfig where
  key : PrivKey
  transports : List Streams.Transport
  securities : List SecurityProtocol
  muxers : List Muxer
  handlers : List StreamHandler
  gater : ConnectionGater
  resourceManager : ResourceManager
  addressRanker : AddressRanker

/-- A host interface for orchestration tests; none of its fields exposes mutable state. -/
structure Host where
  id : PeerId
  startListening : Multiaddr → ExceptT HostError Conc.Async Multiaddr
  addAddrs : PeerId → List Multiaddr → Conc.Async Unit
  dial : Multiaddr → Option PeerId → ExceptT HostError Conc.Async PeerId
  dialPeer : PeerId → ExceptT HostError Conc.Async Unit
  newStreamTo : PeerId → ProtocolId → ExceptT HostError Conc.Async Streams.Stream
  setHandler : StreamHandler → Conc.Async Unit
  close : Conc.Async Unit

/-- Real identity construction will use the key-generation facade and its own checks. -/
opaque generateIdentity : ExceptT HostError Conc.Async PrivKey :=
  throw (unavailable "libp2p/identity and Crypto")

/-- The Noise static key must be fresh for each host. -/
opaque generateStatic : ExceptT HostError Conc.Async Key32 :=
  throw (unavailable "Crypto")

/-- Ping payload generation has no deterministic fallback at program entry. -/
opaque randomPayload : ExceptT HostError Conc.Async ByteArray :=
  throw (unavailable "Crypto")

/-- Host construction fails explicitly until the implementation exists. -/
opaque Host.new (_config : HostConfig) : ExceptT HostError Conc.Async Host :=
  throw (unavailable "libp2p/host")

/-- TCP's W4.2 implementation remains a dependency, despite the merged stream types. -/
opaque tcpTransport : Streams.Transport :=
  { handles := fun _ => false
    dial := fun _ => throw (IO.userError "TCP is not integrated")
    listen := fun _ => throw (IO.userError "TCP is not integrated") }

/-- Noise advertises its id through the seam; it negotiates no muxer extension here. -/
opaque noiseSecurity (_key : PrivKey) (_static : Key32) : SecurityProtocol :=
  { id := ⟨"/noise"⟩
    handshake := fun _ _ _ => throw (.closed "Noise is not integrated") }

/-- W5.8 composes yamux alone; mplex remains P2. -/
opaque yamux : Muxer :=
  { id := ⟨"/yamux/1.0.0"⟩
    «open» := fun _ _ _ => throw (.closed "yamux is not integrated") }

namespace Ping

/-- The identifier is owned by the protocol dependency. -/
opaque protocolId : ProtocolId := ⟨"/ipfs/ping/1.0.0"⟩

/-- The protocol package supplies the handler. -/
opaque pingHandler : StreamHandler :=
  ⟨protocolId, fun _ => throw (.closed "ping is not integrated")⟩

/-- The protocol client checks its echo; the CLI only reports its result. -/
opaque ping (_stream : Streams.Stream) (_clock : Conc.Clock) (_payload : ByteArray) :
    ExceptT HostError Conc.Async Nat := throw (unavailable "ping")

end Ping

namespace Identify

/-- The identifier is owned by the protocol dependency. -/
opaque protocolId : ProtocolId := ⟨"/ipfs/id/1.0.0"⟩

/-- A host-specific handler supplies its current addresses when called. -/
opaque handler (_host : Host) : StreamHandler :=
  ⟨protocolId, fun _ => throw (.closed "identify is not integrated")⟩

/-- Only the metadata the demo prints crosses the client seam. -/
structure Result where
  peer : PeerId
  addressCount : Nat
  protocolCount : Nat

/-- Validation and the peer-id check stay in the protocol implementation. -/
opaque request (_stream : Streams.Stream) (_expected : PeerId) :
    ExceptT HostError Conc.Async Result := throw (unavailable "identify")

end Identify

namespace Echo

/-- The demo echo id belongs with its handler, in protocol test support. -/
opaque protocolId : ProtocolId := ⟨"/demo/echo/1.0.0"⟩

/-- The demo receives the protocol package's handler value. -/
opaque handler : StreamHandler :=
  ⟨protocolId, fun _ => throw (.closed "echo is not integrated")⟩

/-- Echo framing and validation belong to protocol test support. -/
opaque exchange (_stream : Streams.Stream) (_payload : ByteArray) :
    ExceptT HostError Conc.Async ByteArray := throw (unavailable "echo")

end Echo

end CliApp.Mock
