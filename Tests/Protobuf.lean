import Tests.Support
import LeanP2P.Crypto.Messages

/-!
# Protobuf suite (VECTOR_TEST_PLAN.md, phase 2 step 12)

- Wire codec: round trips over mixed messages (including unknown fields)
  and rejected garbage; the `decode_encode` theorem backs every accepted
  message computationally.
- Message vectors from `Tests/vectors/protobuf-messages.json`: Identify,
  NoiseHandshakePayload, PeerRecord, Envelope - decoded into the expected
  structure and re-encoded byte-exactly.
- Key protobuf vectors from the peer-ids spec: `PublicKey` / `PrivateKey`
  bytes unmarshal into the right type and key data.
-/

open LeanP2P Tests

namespace Tests

private def checkRoundTrip (r : Runner) (name : String) (fs : Pb.Fields) :
    IO Unit := do
  r.check s!"pb round trip {name}" (Pb.decodeFields (Pb.encodeFields fs) == some fs)

def Protobuf.run (r : Runner) : IO Unit := do
  r.section "protobuf" "wire format; message vectors generated from the \
vendored spec field tables (Tests/vectors/protobuf-messages.json); key \
vectors from peer-ids spec (keys-peer-ids.json)"

  -- computational shadow of the verified round trip
  let sample : Pb.Fields :=
    [(1, .varint 0), (1, .varint 1), (2, .varint 300),
     (3, .fixed64 0x0102030405060708), (4, .bytes [1, 2, 3, 4, 5]),
     (5, .fixed32 0x04030201), (900, .varint 127), (900, .varint 128)]
  r.check "pb round trip mixed sample"
    (Pb.decodeFields (Pb.encodeFields sample) == some sample)

  checkRoundTrip r "empty" []
  checkRoundTrip r "varints" [(1, .varint 0), (1, .varint 1), (2, .varint 300),
    (3, .varint 9007199254740991)]
  checkRoundTrip r "fixed64/32" [(1, .fixed64 0x0102030405060708),
    (2, .fixed32 0x04030201)]
  checkRoundTrip r "bytes" [(4, .bytes [1, 2, 3, 4, 5]), (4, .bytes []),
    (5, .bytes [255])]
  checkRoundTrip r "unknown fields kept" [(7, .varint 42), (8, .bytes [9, 9]),
    (9, .fixed64 5), (10, .fixed32 6), (11, .bytes [])]
  checkRoundTrip r "submessage" [(4, .bytes (Pb.encodeFields [(1, .varint 7)]))]
  checkRoundTrip r "high field number" [(536870911, .varint 1)]

  -- rejected garbage
  r.check "pb rejects truncated varint key"
    (Pb.decodeFields [0x80] == none)
  r.check "pb rejects wire type 3 (groups)"
    (Pb.decodeFields [0x1b, 0x01] == none)  -- field 3, wire type 3
  r.check "pb rejects wire type 4"
    (Pb.decodeFields [0x1c] == none)
  r.check "pb rejects truncated fixed64"
    (Pb.decodeFields [0x09, 0x01, 0x02] == none)
  r.check "pb rejects truncated bytes length"
    (Pb.decodeFields [0x0a, 0x05, 0x01] == none)
  r.check "pb rejects a lone tag"
    (Pb.decodeFields [0x0a] == none)

  -- message vectors: decode to the expected structure, re-encode exactly
  let j ← loadJson "protobuf-messages.json"
  let exp ← jObj "protobuf-messages.json" j "expected"
  let expVersion ← jStr "protobuf-messages.json" exp "protocolVersion"
  let expAgent ← jStr "protobuf-messages.json" exp "agentVersion"
  let expAddrs ← jStrs "protobuf-messages.json" exp "listenAddrsHex"
  let expObserved ← jStr "protobuf-messages.json" exp "observedAddrHex"
  let expProtocols ← jStrs "protobuf-messages.json" exp "protocols"
  let expMuxers ← jStrs "protobuf-messages.json" exp "streamMuxers"
  let expSeq ← jNat "protobuf-messages.json" exp "seq"
  let expPayloadType ← jStr "protobuf-messages.json" exp "payloadTypeHex"

  let cases ← jArr "protobuf-messages.json" j "cases"
  let mut peerRecordBytes : ByteArray := ByteArray.empty
  for c in cases do
    let name ← jStr "protobuf-messages.json" c "name"
    let bytes ← hexBytesByteArray (← jStr "protobuf-messages.json" c "bytesHex")

    if name.startsWith "Identify" then
      match Messages.decodeIdentify? bytes with
      | none => r.check s!"identify decode {name}" false
      | some m =>
          r.check s!"identify protocolVersion {name}" (m.protocolVersion == some expVersion)
          r.check s!"identify agentVersion {name}" (m.agentVersion == some expAgent)
          r.check s!"identify publicKey present {name}" (m.publicKey.isSome)
          let expAddrsBA ← expAddrs.mapM hexBytesByteArray
          r.check s!"identify listenAddrs {name}"
            (m.listenAddrs.map Bytes.ofNatList == expAddrsBA)
          r.check s!"identify observedAddr {name}"
            (m.observedAddr.map Bytes.ofNatList == some (← hexBytesByteArray expObserved))
          r.check s!"identify protocols {name}" (m.protocols == expProtocols)
          r.check s!"identify re-encode {name}"
            (Messages.encodeIdentifyB m == bytes)

    if name.startsWith "Noise" then
      match Messages.decodeNoisePayload? bytes with
      | none => r.check s!"noise decode {name}" false
      | some p =>
          r.check s!"noise identityKey present {name}" (p.identityKey.length = 36)
          r.check s!"noise identitySig length {name}" (p.identitySig.length = 64)
          match p.extensions with
          | none => r.check s!"noise extensions {name}" false
          | some e =>
              r.check s!"noise streamMuxers {name}" (e.streamMuxers == expMuxers)
              r.check s!"noise certhashes empty {name}" (e.webtransportCerthashes = [])
          r.check s!"noise re-encode {name}"
            (Messages.encodeNoisePayloadB p == bytes)

    if name.startsWith "PeerRecord" then
      match Messages.decodePeerRecord? bytes with
      | none => r.check s!"peerrecord decode {name}" false
      | some rec' =>
          r.check s!"peerrecord seq {name}" (rec'.seq == expSeq)
          r.check s!"peerrecord peerId inlined {name}"
            (rec'.peerId.size = 38 ∧ rec'.peerId.toList.head? = some 0)
          let expAddrsBA2 ← expAddrs.mapM hexBytesByteArray
          r.check s!"peerrecord addrs {name}"
            (rec'.addresses == expAddrsBA2)
          r.check s!"peerrecord re-encode {name}"
            (Messages.encodePeerRecordB rec' == bytes)
      peerRecordBytes := bytes

    if name.startsWith "Envelope" then
      match Messages.decodeEnvelope? bytes with
      | none => r.check s!"envelope decode {name}" false
      | some e =>
          let expPayloadTypeBA ← hexBytesByteArray expPayloadType
          r.check s!"envelope payloadType {name}"
            (e.payloadType == expPayloadTypeBA)
          r.check s!"envelope payload is the peer record {name}"
            (e.payload == peerRecordBytes)
          r.check s!"envelope re-encode {name}"
            (Messages.encodeEnvelopeB e == bytes)

  -- key protobuf vectors (go-libp2p-produced bytes from the peer-ids spec)
  let kj ← loadJson "keys-peer-ids.json"
  for k in (← jArr "keys-peer-ids.json" kj "keys") do
    let name ← jStr "keys-peer-ids.json" k "name"
    let bytes ← hexBytesByteArray (← jStr "keys-peer-ids.json" k "bytesHex")
    if name.contains "private" then
      match Keys.unmarshalPrivKey? bytes with
      | none => r.check s!"key unmarshal {name}" false
      | some priv =>
          r.check s!"key round trip {name}"
            (Keys.marshalPrivKey priv == bytes)
    else
      match Keys.unmarshalPubKey? bytes with
      | none => r.check s!"key unmarshal {name}" false
      | some pub =>
          r.check s!"key round trip {name}"
            (Keys.marshalPubKey pub == bytes)

end Tests
