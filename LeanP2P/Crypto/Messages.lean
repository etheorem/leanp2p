import LeanP2P.Crypto.Keys
/-!
# libp2p protobuf messages (VECTOR_TEST_PLAN.md, phase 2 step 12)

Encode/decode for the messages phase 2 and 3 need, on top of `Crypto/Pb`:

- `Identify` (vendor/specs/identify/README.md): protocolVersion 5,
  agentVersion 6, publicKey 1, listenAddrs 2 (repeated), observedAddr 4,
  protocols 3 (repeated).
- `NoiseHandshakePayload` (vendor/specs/noise/README.md): identity_key 1,
  identity_sig 2, extensions 4 (message; webtransport_certhashes 1
  repeated, stream_muxers 2 repeated).
- `Envelope` (RFC 0002): public_key 1, payload_type 2, payload 3,
  signature 5; signature input is uvarint-prefixed domain, payload type,
  payload.
- `PeerRecord` (RFC 0003): peer_id 1, seq 2, addresses 3 (repeated
  AddressInfo{ multiaddr 1 }); payload type 0x0301, domain
  `libp2p-peer-record`.

Byte vectors for all of these live in `Tests/vectors` and are exercised by
`Tests/Protobuf` (go-libp2p-produced key vectors from the peer-ids spec,
plus message vectors generated from these field tables by an independent
encoder in `scripts/extract-vectors.py`).
-/

namespace LeanP2P.Messages

open Pb

/-! ## Identify -/

structure IdentifyMsg where
  protocolVersion : Option String
  agentVersion : Option String
  publicKey : Option (List Nat)   -- serialized PublicKey message
  listenAddrs : List (List Nat)   -- binary multiaddrs
  observedAddr : Option (List Nat)
  protocols : List String
  deriving Repr, BEq

def encodeIdentify (m : IdentifyMsg) : Fields :=
  (m.protocolVersion.toList.map (fun s => (5, .bytes (Bytes.toNatList (Bytes.ofString s))))) ++
  (m.agentVersion.toList.map (fun s => (6, .bytes (Bytes.toNatList (Bytes.ofString s))))) ++
  (m.publicKey.toList.map (fun k => (1, .bytes k))) ++
  (m.listenAddrs.map (fun a => (2, .bytes a))) ++
  (m.observedAddr.toList.map (fun a => (4, .bytes a))) ++
  (m.protocols.map (fun p => (3, .bytes (Bytes.toNatList (Bytes.ofString p)))))

def encodeIdentifyB (m : IdentifyMsg) : ByteArray := encodeFieldsB (encodeIdentify m)

def decodeIdentify? (b : ByteArray) : Option IdentifyMsg := do
  let fs ← decodeFieldsB? b
  pure {
    protocolVersion := getStr? 5 fs
    agentVersion := getStr? 6 fs
    publicKey := getBytes? 1 fs
    listenAddrs := getAllBytes 2 fs
    observedAddr := getBytes? 4 fs
    protocols := getAllStrs 3 fs
  }

/-! ## NoiseHandshakePayload -/

structure NoiseExtensions where
  webtransportCerthashes : List (List Nat)
  streamMuxers : List String
  deriving Repr, BEq

structure NoiseHandshakePayload where
  identityKey : List Nat      -- serialized PublicKey message
  identitySig : List Nat      -- signature of `noise-libp2p-static-key:` ++
                              -- static Noise key, under the identity key
  extensions : Option NoiseExtensions
  deriving Repr, BEq

def encodeNoisePayload (p : NoiseHandshakePayload) : Fields :=
  [(1, .bytes p.identityKey), (2, .bytes p.identitySig)] ++
  p.extensions.toList.map (fun e =>
    (4, .bytes (encodeFields
      (e.webtransportCerthashes.map (fun c => (1, .bytes c)) ++
        e.streamMuxers.map (fun m =>
          (2, .bytes (Bytes.toNatList (Bytes.ofString m))))))))

def encodeNoisePayloadB (p : NoiseHandshakePayload) : ByteArray :=
  encodeFieldsB (encodeNoisePayload p)

def decodeNoiseExtensions? (fs : Fields) : Option NoiseExtensions :=
  pure { webtransportCerthashes := getAllBytes 1 fs
         streamMuxers := getAllStrs 2 fs }

def decodeNoisePayload? (b : ByteArray) : Option NoiseHandshakePayload := do
  let fs ← decodeFieldsB? b
  let identityKey ← getBytes? 1 fs
  let identitySig ← getBytes? 2 fs
  let extensions ← (getSub? 4 fs).mapM decodeNoiseExtensions?
  pure { identityKey, identitySig, extensions }

/-! ## Envelope (RFC 0002) -/

structure Envelope where
  publicKey : ByteArray     -- serialized PublicKey message
  payloadType : ByteArray   -- multicodec(-prefixed) type indicator
  payload : ByteArray
  signature : ByteArray
  deriving Repr, BEq

def encodeEnvelope (e : Envelope) : Fields :=
  [(1, .bytes (Bytes.toNatList e.publicKey)),
   (2, .bytes (Bytes.toNatList e.payloadType)),
   (3, .bytes (Bytes.toNatList e.payload)),
   (5, .bytes (Bytes.toNatList e.signature))]

def encodeEnvelopeB (e : Envelope) : ByteArray := encodeFieldsB (encodeEnvelope e)

def decodeEnvelope? (b : ByteArray) : Option Envelope := do
  let fs ← decodeFieldsB? b
  let publicKey ← getBytes? 1 fs
  let payloadType ← getBytes? 2 fs
  let payload ← getBytes? 3 fs
  let signature ← getBytes? 5 fs
  pure { publicKey := Bytes.ofNatList publicKey
         payloadType := Bytes.ofNatList payloadType
         payload := Bytes.ofNatList payload
         signature := Bytes.ofNatList signature }

/-- RFC 0002 signature input: uvarint(domain) ++ domain ++
uvarint(payloadType) ++ payloadType ++ uvarint(payload) ++ payload. -/
def Envelope.signatureInput (domain : String) (e : Envelope) : ByteArray :=
  let d := Bytes.toNatList (Bytes.ofString domain)
  Bytes.ofNatList
    (Varint.encode d.length ++ d ++
      Varint.encode e.payloadType.size ++ Bytes.toNatList e.payloadType ++
      Varint.encode e.payload.size ++ Bytes.toNatList e.payload)

/-- Sign an envelope with a private key under `domain`. The public key is
not part of the signature input (RFC 0002). -/
def Envelope.sign (domain : String) (priv : Keys.PrivKey) (payloadType : ByteArray)
    (payload : ByteArray) : IO (Option Envelope) := do
  match ← priv.publicKey with
  | none => pure none
  | some pub =>
      let env : Envelope :=
        { publicKey := Keys.marshalPubKey pub, payloadType, payload,
          signature := ByteArray.empty }
      let input := env.signatureInput domain
      match ← priv.sign input with
      | some sig => pure (some { env with signature := sig })
      | none => pure none

/-- Verify an envelope's signature under `domain` against its embedded
public key. -/
def Envelope.verify (domain : String) (e : Envelope) : IO Bool := do
  match Keys.unmarshalPubKey? e.publicKey with
  | none => pure false
  | some pub => pub.verify (e.signatureInput domain) e.signature

/-! ## PeerRecord (RFC 0003) -/

def peerRecordDomain : String := "libp2p-peer-record"

/-- multicodec payload type of PeerRecord. -/
def peerRecordPayloadType : ByteArray := Bytes.ofNatList [0x03, 0x01]

structure PeerRecord where
  peerId : ByteArray       -- binary peer id (multihash bytes)
  seq : Nat
  addresses : List (ByteArray)  -- binary multiaddrs
  deriving Repr, BEq

def encodePeerRecord (r : PeerRecord) : Fields :=
  [(1, .bytes (Bytes.toNatList r.peerId)), (2, .varint r.seq)] ++
  r.addresses.map (fun a =>
    (3, .bytes (encodeFields [(1, .bytes (Bytes.toNatList a))])))

def encodePeerRecordB (r : PeerRecord) : ByteArray :=
  encodeFieldsB (encodePeerRecord r)

def decodePeerRecord? (b : ByteArray) : Option PeerRecord := do
  let fs ← decodeFieldsB? b
  let peerId ← getBytes? 1 fs
  let seq ← getVarint? 2 fs
  let addresses ←
    (getAllBytes 3 fs).mapM (fun a => do
      let info ← decodeFields a
      getBytes? 1 info)
  pure { peerId := Bytes.ofNatList peerId, seq, addresses := addresses.map Bytes.ofNatList }

/-- Wrap a peer record in a signed envelope (RFC 0003 certification). -/
def PeerRecord.envelope (r : PeerRecord) (priv : Keys.PrivKey) :
    IO (Option Envelope) :=
  Envelope.sign peerRecordDomain priv peerRecordPayloadType
    (encodePeerRecordB r)

/-- Open and fully validate a signed peer record: the envelope's
`payload_type` must be the PeerRecord multicodec (RFC 0002: the type
identifies how to interpret the payload - verifying the signature while
ignoring it would let any payload through as a "peer record"), then the
signature, then the peer id against the envelope's embedded key. -/
def PeerRecord.verifyEnvelope? (e : Envelope) : IO (Option PeerRecord) := do
  if e.payloadType != peerRecordPayloadType then pure none
  else if ← e.verify peerRecordDomain then
    match decodePeerRecord? e.payload with
    | none => pure none
    | some r =>
        match Keys.unmarshalPubKey? e.publicKey with
        | none => pure none
        | some pub =>
            if (PeerId.ofPublicKey pub).bytes == r.peerId then
              pure (some r)
            else pure none
  else pure none

end LeanP2P.Messages
