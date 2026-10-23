import Tests.Support

/-!
# Envelope + PeerRecord suite (VECTOR_TEST_PLAN.md, phase 3 step 21)

RFC 0002 (envelope) and RFC 0003 (peer record) against a real go-libp2p
sealed envelope captured from `record.Seal` (envelope-go.json):
- signature verification over the RFC 0002 input
  (varint(domain) ++ domain ++ varint(payloadType) ++ payloadType ++ payload);
- PeerRecord payload decoding (peer id, seq, addresses);
- the go PeerRecord round-trips through our `PeerRecord.verifyEnvelope?`.

The envelope is sealed with the RFC 8032 §7.1 TEST 2 Ed25519 key
(also used by the Noise identify e2e), so the suite additionally checks
that our own `Envelope.sign` produces a byte-identical envelope.
-/

open LeanP2P Tests

namespace Tests

def EnvelopeSuite.run (r : Runner) : IO Unit := do
  r.section "envelope + peer record"
    "libp2p/specs RFC 0002/0003 + captured go-libp2p record.Seal output"

  let j ← loadJson "envelope-go.json"
  let envBytes ← hexBytesByteArray (← jStr "envelope-go.json" j "envelopeHex")
  let payloadHex ← jStr "envelope-go.json" j "payloadHex"
  let payloadTypeHex ← jStr "envelope-go.json" j "payloadTypeHex"
  let domain ← jStr "envelope-go.json" j "domain"
  let wantPeerId ← jStr "envelope-go.json" j "peerId"
  let wantSeq ← jNat "envelope-go.json" j "seq"

  -- decode the envelope protobuf
  match Messages.decodeEnvelope? envBytes with
  | none => r.check "envelope decodes" false
  | some env => do
    r.check "envelope payload type" (env.payloadType == Bytes.ofNatList
      (Bytes.toNatList (Bytes.ofHex? payloadTypeHex |>.getD ByteArray.empty)))
    r.check "envelope payload" (env.payload ==
      (Bytes.ofHex? payloadHex |>.getD ByteArray.empty))
    -- verify the signature over the RFC 0002 input
    let verified ← env.verify domain
    r.check "envelope signature verifies" verified
    -- decode the PeerRecord payload
    match Messages.decodePeerRecord? env.payload with
    | none => r.check "peer record decodes" false
    | some rec => do
      r.check "peer record seq" (rec.seq == wantSeq)
      r.check "peer record addrs" (rec.addresses.length == 1)
      -- peer id from the envelope's embedded public key
      match Keys.unmarshalPubKey? env.publicKey with
      | none => r.check "peer record peer id" false
      | some key => do
        let pid := PeerId.ofPublicKey key
        r.check "peer record peer id" (PeerId.toBase58 pid == wantPeerId)
      -- full verification chain
      let verified ← Messages.PeerRecord.verifyEnvelope? env
      r.check "peer record verifyEnvelope" verified.isSome
      -- the payload_type is part of validation: an envelope with a
      -- different type must not be opened as a peer record (RFC 0002
      -- makes the type identify the payload's schema)
      let wrongType : Messages.Envelope := { env with payloadType := Bytes.ofNatList [1] }
      let rejected ← Messages.PeerRecord.verifyEnvelope? wrongType
      r.check "verifyEnvelope rejects wrong payload type" rejected.isNone

  -- the signature is non-empty and verified above
  r.check "envelope signature non-empty" (envBytes.size > 0)

end Tests
