import Proto
import Libp2p.Identity
import Libp2p.Security.Constants
import Libp2p.Security.Handshake

/-!
# The libp2p handshake payload

The second and third Noise messages carry a `NoiseHandshakePayload`
(the noise-libp2p spec, "The libp2p Handshake Payload"):

```protobuf
message NoiseHandshakePayload {
  optional bytes identity_key = 1;
  optional bytes identity_sig = 2;
  optional NoiseExtensions extensions = 4;
}
```

`identity_key` is a marshaled `PublicKey` (the peer-ids spec), and
`identity_sig` signs the string `noise-libp2p-static-key:` followed by
the static Noise public key. The spec says: "Upon receiving the
handshake payload, peers MUST decode the public key … The key MUST then
be used to validate the `identity_sig` field against the static Noise
key received in the handshake." `verify` does both, and gives the
`PeerId` the key derives.

**The 8 KiB gate.** `decode?` refuses a payload over `maxPayload`
before the protobuf decode runs (owned contract 2, §5.1).

**The extensions stay opaque** (the package ARCHITECTURE, "The
handshake extensions"). The decode keeps field 4 as bytes, and the
payload we build carries none.
-/

set_option autoImplicit false

namespace Libp2p.Security.Noise

open Bytes Libp2p.Identity

/-- The bytes of one present payload field, with the varint budget of
its length prefix (`Pb.Value.Valid`), so `toFields` needs no check. -/
structure Field where
  /-- The bytes. -/
  bytes : ByteArray
  /-- The length fits its varint prefix. -/
  lt : bytes.size < Varint.limit

/-- The field of the bytes. `none` only past the varint budget, which no
`ByteArray` in memory reaches. -/
def Field.ofByteArray? (b : ByteArray) : Option Field :=
  if h : b.size < Varint.limit then some ⟨b, h⟩ else none

instance : Repr Field where
  reprPrec f _ := s!"Noise.Field {toHex f.bytes}"

/-- One `NoiseHandshakePayload`. Every field is `optional` in the spec
schema, so each one may be absent. -/
structure HandshakePayload where
  /-- `identity_key`: the marshaled identity `PublicKey`. -/
  identityKey : Option Field
  /-- `identity_sig`: the signature over the static Noise key. -/
  identitySig : Option Field
  /-- `extensions`, kept as the bytes of the submessage. -/
  extensions : Option Field
  deriving Repr

namespace HandshakePayload

/-- The entry of one optional field: one entry when present, none when
absent. `codec/proto` carries a payload in the `List Nat` byte model, so
the bytes enter through `toNatList`. -/
private def entry (n : Nat) : Option Field → List Pb.Entry
  | some f => [(n, .bytes (toNatList f.bytes))]
  | none => []

private theorem entryValid (n : Nat) (h0 : 0 < n) (h1 : n < Pb.fieldNumberLimit)
    (x : Option Field) : ∀ e ∈ entry n x, e.Valid := by
  cases x with
  | none => simp [entry]
  | some f =>
    simp only [entry, List.mem_cons, List.not_mem_nil, or_false]
    rintro e rfl
    refine ⟨h0, h1, ?_, fun _ hx => ltOfMemToNatList hx⟩
    rw [lengthToNatList]
    exact f.lt

/-- The entries in field order. -/
def toFields (p : HandshakePayload) : Pb.Fields where
  entries := entry identityKeyField p.identityKey ++ entry identitySigField p.identitySig ++
    entry extensionsField p.extensions
  valid := by
    intro e he
    simp only [List.mem_append] at he
    -- The field numbers 1, 2, and 4 are in the spec range; `decide`
    -- unfolds the constants and compares them with `2 ^ 29`.
    rcases he with (he | he) | he
    · exact entryValid _ (by decide) (by decide) _ e he
    · exact entryValid _ (by decide) (by decide) _ e he
    · exact entryValid _ (by decide) (by decide) _ e he

/-- A present field of the decoded entries. A field of the wrong wire
type reads as absent, as `Pb.getBytes?` reads it. -/
private def field? (fs : Pb.Fields) (n : Nat) : Option Field :=
  (Pb.getBytes? n fs).bind fun l => Field.ofByteArray? (ofNatList l)

/-- Every field is optional, so the table rejects no entry list. -/
def ofFields (fs : Pb.Fields) : HandshakePayload where
  identityKey := field? fs identityKeyField
  identitySig := field? fs identitySigField
  extensions := field? fs extensionsField

end HandshakePayload

instance : Pb.ProtoMessage HandshakePayload where
  toFields := HandshakePayload.toFields
  ofFields? fs := .ok (HandshakePayload.ofFields fs)

/-- A field reads back from its own bytes: the size check passes on
`f.lt`, and structure eta rebuilds `f`. -/
private theorem Field.ofByteArray?Bytes (f : Field) : Field.ofByteArray? f.bytes = some f := by
  simp [Field.ofByteArray?, f.lt]

/-- The table reads back its own entries. Each field is absent or
present, so eight cases; in each one the lookup of a field number finds
the one entry `toFields` wrote for it. -/
theorem HandshakePayload.ofFieldsToFields (p : HandshakePayload) :
    HandshakePayload.ofFields (HandshakePayload.toFields p) = p := by
  obtain ⟨k, s, x⟩ := p
  cases k <;> cases s <;> cases x <;>
    simp [HandshakePayload.ofFields, HandshakePayload.toFields, HandshakePayload.field?,
      HandshakePayload.entry, Pb.getBytes?, Pb.lookupLast, List.lookup, identityKeyField,
      identitySigField, extensionsField, ofNatListToNatList, Field.ofByteArray?Bytes]

/-- A payload decodes back to itself over the byte model, with no input
left: the wire round trip of `codec/proto` (`Pb.decodeEncode`), then the
table's own. -/
theorem HandshakePayload.decodeEncode (p : HandshakePayload) :
    Pb.decodeMessage? (Pb.encodeMessage p) = .ok (p, []) := by
  -- The instance's `ofFields?` is `.ok ∘ ofFields`, so after the wire
  -- round trip the table's own round trip closes the goal.
  simp only [Pb.decodeMessage?, Pb.encodeMessage, Pb.ProtoMessage.toFields,
    Pb.ProtoMessage.ofFields?, Pb.decodeEncode, bind, Except.bind,
    HandshakePayload.ofFieldsToFields]

/-- The signed data: `noise-libp2p-static-key:`, then the static Noise
public key. -/
def signatureInput (staticPub : Bytes32) : ByteArray :=
  staticKeyPrefix.toUTF8 ++ staticPub.bytes

/-- The payload of the bytes. A payload over `maxPayload` is refused
before the decode runs (owned contract 2). -/
def HandshakePayload.decode? (b : ByteArray) : Except Error HandshakePayload :=
  if b.size > maxPayload then .error (.payloadTooLarge b.size)
  -- `decodeMessageB?` reads the whole buffer, so the count it answers
  -- is `b.size`, and only the message stays.
  else ((Pb.decodeMessageB? b).map Prod.fst).mapError .payload

/-- What a payload proved: the identity key, the peer id it derives,
and the opaque extensions. -/
structure Verified where
  /-- The identity key of the peer. -/
  key : PubKey
  /-- The peer id of the identity key. -/
  peer : PeerId
  /-- The bytes of the `extensions` submessage, when present. -/
  extensions : Option Blob
  deriving Repr

/-- Check the peer's payload against the static key of the handshake:
the gate and the decode, then the identity key, then the signature. A
failure ends the connection (the spec: "If the signature is invalid,
the connection MUST be terminated immediately"). -/
def verify (remoteStatic : Bytes32) (b : ByteArray) : Except Error Verified := do
  let p ← HandshakePayload.decode? b
  let some k := p.identityKey | throw .missingIdentity
  let some sig := p.identitySig | throw .missingIdentity
  let key ← (PubKey.unmarshal? k.bytes).mapError .identity
  unless key.verify (signatureInput remoteStatic) sig.bytes do throw .badSignature
  let peer ← (PeerId.ofPubKey key).mapError .identity
  return { key, peer, extensions := p.extensions.map fun f => ⟨f.bytes⟩ }

/-- Our payload: the marshaled identity key, and its signature over our
static Noise key. It carries no extensions. `sign` runs in `IO`,
because secp256k1 and ECDSA draw a nonce (§3.6). -/
def build (identity : PrivKey) (staticPub : Bytes32) : ExceptT Error IO ByteArray := do
  let pub ← ExceptT.mk (pure (identity.toPublic.mapError .identity))
  let sig ← (identity.sign (signatureInput staticPub)).adapt .identity
  -- Neither field reaches the varint budget, so both checks pass.
  let some kf := Field.ofByteArray? pub.marshal | throw (.payloadTooLarge pub.marshal.size)
  let some sf := Field.ofByteArray? sig | throw (.payloadTooLarge sig.size)
  return Pb.encodeMessageB
    ({ identityKey := some kf, identitySig := some sf, extensions := none } : HandshakePayload)

end Libp2p.Security.Noise
