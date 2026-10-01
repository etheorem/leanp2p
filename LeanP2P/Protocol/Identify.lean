import LeanP2P.Conn.Stream
import LeanP2P.Crypto.Keys
import LeanP2P.Crypto.Messages
import LeanP2P.Net.Multiaddr
import LeanP2P.Net.Varint
import LeanP2P.Conn.Reader
import LeanP2P.Crypto.Bytes
/-!
# Identify protocol (VECTOR_TEST_PLAN.md, phase 3 step 20)

Per vendor/specs/identify/README.md: the protocol id is `/ipfs/id/1.0.0`
(push variant `/ipfs/id/push/1.0.0`). The responder sends an `Identify`
protobuf message (vendor/specs/identify identifies/identify.proto):

    message Identify {
      optional string protocolVersion = 5;  // "/ipfs/1.0.0"
      optional string agentVersion = 6;
      optional bytes publicKey = 1;         // the peer's public key
      repeated bytes listenAddrs = 2;       // multiaddrs
      optional bytes observedAddr = 4;      // the caller's observed address
      repeated string protocols = 3;        // supported protocols
    }

The dialer verifies that the peer id derived from `publicKey` matches the
peer it connected to (peer-ids spec).
-/

namespace LeanP2P.Identify

def protocol : String := "/ipfs/id/1.0.0"
def protocolPush : String := "/ipfs/id/push/1.0.0"
def protocolVersion : String := "/ipfs/1.0.0"

/-- Build the responder's Identify message. The public key is embedded as
the serialized `PublicKey` protobuf (peer-ids spec). -/
def respond (key : Keys.PubKey) (addrs : List Multiaddr) (protocols : List String)
    (observed : Option Multiaddr) (agent : String) : Messages.IdentifyMsg where
  protocolVersion := some protocolVersion
  agentVersion := some agent
  publicKey := some (Bytes.toNatList (Keys.marshalPubKey key))
  listenAddrs := addrs.map (fun a => Bytes.toNatList (Multiaddr.encodeBinB a.components))
  observedAddr := observed.map (fun a => Bytes.toNatList (Multiaddr.encodeBinB a.components))
  protocols := protocols

/-- Responder: serialize the Identify message, prefix with a uvarint
length (go/rust RPC framing), and send. -/
def respondAndSend (key : Keys.PubKey) (addrs : List Multiaddr) (protocols : List String)
    (observed : Option Multiaddr) (agent : String) (s : Stream) : IO Unit := do
  let msg := respond key addrs protocols observed agent
  let bytes := Messages.encodeIdentifyB msg
  s.write (Bytes.ofNatList (Varint.encode bytes.size) ++ bytes)
  s.close

/-- Strip the uvarint RPC length prefix from a go-libp2p Identify response. -/
def stripLengthPrefix (b : ByteArray) : ByteArray :=
  match Varint.decodeB? b 0 with
  | some (_, offset) => b.extract offset b.size
  | none => b

/-- Read a uvarint from the buffered reader (one byte at a time). -/
partial def readUvarintB (r : BufReader) : IO (Option Nat) := do
  let rec loop (fuel shift value : Nat) : IO (Option Nat) := do
    if fuel = 0 then
      return (Option.none : Option Nat)
    match ← BufReader.readExactly r 1 with
    | none =>
      return (Option.none : Option Nat)
    | some byte =>
      let b := byte[0]!.toNat
      let v := value ||| ((b % 128) <<< shift)
      if b < 128 then
        pure (some v)
      else
        loop (fuel - 1) (shift + 7) v
  loop 9 0 0

/-- Initiator: read one length-delimited Identify message through a
buffered reader. The uvarint length prefix is consumed, then the declared
number of protobuf bytes is read exactly. The peer id is derived from the
serialized `PublicKey` protobuf. -/
def requestR (r : BufReader) : IO (Option (Messages.IdentifyMsg × PeerId)) := do
  let lenOpt ← readUvarintB r
  match lenOpt with
  | none => return none
  | some len =>
    if len = 0 || len > 65536 then return none
    match ← BufReader.readExactly r len with
    | none => return none
    | some protobuf =>
      match Messages.decodeIdentify? protobuf with
      | none => return none
      | some msg =>
        match msg.publicKey with
        | none => return none
        | some keyBytes =>
          match Keys.unmarshalPubKey? (Bytes.ofNatList keyBytes) with
          | none => return none
          | some key => return (some (msg, PeerId.ofPublicKey key))

/-- Convenience: `requestR` over a bare `Stream`. -/
def request (s : Stream) : IO (Option (Messages.IdentifyMsg × PeerId)) := do
  let r ← BufReader.ofConn
    { read := s.read, write := s.write, close := s.close
      localAddr := { components := [] }, remoteAddr := { components := [] } }
  requestR r

end LeanP2P.Identify
