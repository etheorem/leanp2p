import Tests.Support
import LeanP2P.Crypto.Messages
import LeanP2P.Crypto.OpenSsl

/-!
# Keys and PeerId suite (VECTOR_TEST_PLAN.md, phase 2 step 13)

Mirrors: libp2p peer-ids spec (key vectors + peer-id string examples,
`Tests/vectors/keys-peer-ids.json`), RFC 8032 Ed25519 vectors
(`keys-rfc8032.json`), and the go-libp2p `core/peer` behaviors (id
decode/encode/ToCid/FromCid/IDFromPublicKey) as suite checks.

For every key type in the spec's vector table:
- the private key protobuf derives exactly the public key protobuf
  (the spec's SHOULD check);
- `PeerId.ofPublicKey` follows the 42-byte rule: Ed25519 ids are identity
  multihashes (`12D3KooW...`), RSA ids are sha2-256.
-/

open LeanP2P Tests

namespace Tests

def Keys.run (r : Runner) : IO Unit := do
  r.section "keys + peer ids" "libp2p/specs peer-ids.md key vectors and \
peer-id examples (keys-peer-ids.json); RFC 8032 section 7.1 Ed25519 vectors \
(keys-rfc8032.json); go-libp2p core/peer behaviors"

  let kj ← loadJson "keys-peer-ids.json"
  let mut ed25519PrivBytes : ByteArray := ByteArray.empty
  let mut ed25519PubBytes : ByteArray := ByteArray.empty
  let mut secp256k1PrivBytes : ByteArray := ByteArray.empty
  let mut ecdsaPrivBytes : ByteArray := ByteArray.empty
  let mut rsaPrivBytes : ByteArray := ByteArray.empty

  -- key vectors: private derives public, peer id obeys the 42-byte rule
  for k in (← jArr "keys-peer-ids.json" kj "keys") do
    let name ← jStr "keys-peer-ids.json" k "name"
    let bytes ← hexBytesByteArray (← jStr "keys-peer-ids.json" k "bytesHex")
    if name.contains "private" then
      match Keys.unmarshalPrivKey? bytes with
      | none => r.check s!"priv unmarshal {name}" false
      | some priv =>
          if name.startsWith "ED25519" then ed25519PrivBytes := bytes
          if name.startsWith "secp256k1" then secp256k1PrivBytes := bytes
          if name.startsWith "ECDSA" then ecdsaPrivBytes := bytes
          if name.startsWith "rsa" then rsaPrivBytes := bytes
          match ← priv.publicKey with
          | none => r.check s!"pubkey from priv {name}" false
          | some pub =>
              r.check s!"pubkey from priv {name}" true
              let pubBytes ← jArr "keys-peer-ids.json" kj "keys"
              -- the matching public key vector must equal the derived one
              let derived := Keys.marshalPubKey pub
              let mut matched := false
              for k2 in pubBytes do
                let name2 ← jStr "keys-peer-ids.json" k2 "name"
                if name2 == name.replace "private" "public" then
                  let b2 ← hexBytesByteArray (← jStr "keys-peer-ids.json" k2 "bytesHex")
                  if derived == b2 then matched := true
              r.check s!"derived public key matches vector {name}" matched
    else
      match Keys.unmarshalPubKey? bytes with
      | none => r.check s!"pub unmarshal {name}" false
      | some pub =>
          if name.startsWith "ED25519" then ed25519PubBytes := bytes
          -- 42-byte rule: ed25519 inlines, rsa hashes
          let id := PeerId.ofPublicKey pub
          if pub.keyType = .ed25519 then
            r.check s!"peer id inlined (identity mh) {name}"
              (id.bytes.size = 38 ∧ id.bytes.toList.head? = some 0)
          if pub.keyType = .rsa then
            r.check s!"peer id sha2-256 {name}"
              (id.bytes.extract 0 2 == Bytes.ofNatList [0x12, 0x20])

  -- the three peer-id string examples of the spec
  for e in (← jArr "keys-peer-ids.json" kj "peerIdExamples") do
    let s ← jStr "keys-peer-ids.json" e "string"
    match PeerId.ofString? s with
    | none => r.check s!"peer id parse {s.take 12}..." false
    | some id =>
        r.check s!"peer id parse {s.take 12}..." true
        if s.startsWith "bafz" then
          -- the CID and base58 forms are the same peer id
          match PeerId.ofString? "QmYyQSo1c1Ym7orWxLYvCrM2EmxFTANf8wXmmE7DWjhx5N" with
          | none => r.check "peer id cid = base58 form" false
          | some other =>
              r.check "peer id cid = base58 form" (id.bytes == other.bytes)
        if s.startsWith "12D3KooW" then
          -- the ed25519 example id is an identity multihash (38 bytes) and
          -- re-encodes to exactly the same string
          r.check "peer id example inlined" (id.bytes.size = 38)
          r.check "peer id base58 form matches" (id.toBase58 == s)

  -- both text forms round-trip for every key type with a derived id
  for k in (← jArr "keys-peer-ids.json" kj "keys") do
    let name ← jStr "keys-peer-ids.json" k "name"
    if name.contains "public" then
      let bytes ← hexBytesByteArray (← jStr "keys-peer-ids.json" k "bytesHex")
      match Keys.unmarshalPubKey? bytes with
      | none => r.check s!"peer id forms {name}" false
      | some pub =>
          let id := PeerId.ofPublicKey pub
          match PeerId.ofString? id.toBase58 with
          | none => r.check s!"peer id forms base58 {name}" false
          | some back =>
              r.check s!"peer id forms base58 {name}" (back.bytes == id.bytes)
          let cid := id.toCidString
          match PeerId.ofString? cid with
          | none => r.check s!"peer id forms cidv1 {name}" false
          | some back =>
              r.check s!"peer id forms cidv1 {name}" (back.bytes == id.bytes)

  -- RFC 8032 Ed25519: sign matches the vector, verify accepts it, a
  -- tampered message is rejected
  let rj ← loadJson "keys-rfc8032.json"
  for e in (← jArr "keys-rfc8032.json" rj "ed25519") do
    let name ← jStr "keys-rfc8032.json" e "name"
    let seed ← hexBytesByteArray (← jStr "keys-rfc8032.json" e "seedHex")
    let pub ← hexBytesByteArray (← jStr "keys-rfc8032.json" e "pubHex")
    let msg ← hexBytesByteArray (← jStr "keys-rfc8032.json" e "msgHex")
    let sig ← hexBytesByteArray (← jStr "keys-rfc8032.json" e "sigHex")
    r.check s!"ed25519 derive {name}" ((← OpenSsl.ed25519Pubkey seed) == some pub)
    r.check s!"ed25519 sign {name}" ((← OpenSsl.ed25519Sign seed msg) == some sig)
    r.check s!"ed25519 verify {name}" (← OpenSsl.ed25519Verify pub msg sig)
    let tampered := msg.push 0
    r.check s!"ed25519 rejects tampered {name}" (← (do
      if ← OpenSsl.ed25519Verify pub tampered sig then pure false else pure true))

  -- Ed25519 private key protobuf (64-byte seed||pub) signs like the seed
  match Keys.unmarshalPrivKey? ed25519PrivBytes with
  | none => r.check "ed25519 priv pb sign path" false
  | some priv =>
      let msg := Bytes.ofString "hello libp2p"
      match ← priv.sign msg with
      | none => r.check "ed25519 priv pb sign path" false
      | some sig =>
          match Keys.unmarshalPubKey? ed25519PubBytes with
          | none => r.check "ed25519 priv pb sign path" false
          | some pub => r.check "ed25519 priv pb sign path" (← pub.verify msg sig)

  -- sign/verify round trips per key type (signatures differ per run for
  -- the randomized DER scheme; verification is the contract)
  -- sign/verify round trip for every key type with the spec's own key
  -- (the go-libp2p fixture suite below adds externally produced
  -- signatures; this checks our own)
  for (ty, privBytes, msgBytes) in
      [(Keys.KeyType.ed25519, ed25519PrivBytes, "one"),
        (Keys.KeyType.secp256k1, secp256k1PrivBytes, "two"),
        (Keys.KeyType.ecdsa, ecdsaPrivBytes, "three"),
        (Keys.KeyType.rsa, rsaPrivBytes, "four")] do
    let msg := Bytes.ofString msgBytes
    match Keys.unmarshalPrivKey? privBytes with
    | none => r.check s!"sign/verify {ty}" false
    | some priv =>
        match ← priv.sign msg with
        | none => r.check s!"sign/verify {ty}" false
        | some sig =>
            match ← priv.publicKey with
            | none => r.check s!"sign/verify {ty}" false
            | some pub =>
                r.check s!"sign/verify {ty}" (← pub.verify msg sig)
                let bad := msg.push 33
                r.check s!"sign/verify rejects tampered {ty}"
                  (!(← pub.verify bad sig))

  -- RFC 0002/0003: a signed peer record envelope verifies, derives the
  -- same peer id, and rejects tampering
  match Keys.unmarshalPrivKey? ed25519PrivBytes with
  | none => r.check "envelope round trip" false
  | some priv =>
    match ← priv.publicKey with
    | none => r.check "envelope round trip" false
    | some pub =>
      let id := PeerId.ofPublicKey pub
      let ma1 ← hexToBA "047f000001060fa1"
      let ma2 ← hexToBA "410000000000000000000000000000000001a3020035"
      let rec'' : Messages.PeerRecord :=
        { peerId := id.bytes, seq := 1570215229, addresses := [ma1, ma2] }
      match ← rec''.envelope priv with
      | none => r.check "envelope round trip" false
      | some env =>
          r.check "envelope verifies" (← env.verify Messages.peerRecordDomain)
          match ← Messages.PeerRecord.verifyEnvelope? env with
          | none => r.check "envelope round trip" false
          | some back =>
              r.check "envelope round trip" (back == rec'')
          -- tamper with the payload: verification must fail
          let tampered : Messages.Envelope :=
            { env with payload := env.payload.push 0 }
          r.check "envelope rejects tampered"
            (!(← tampered.verify Messages.peerRecordDomain))

where
  hexToBA (h : String) : IO ByteArray := do
    match Bytes.ofHex? h with
    | some b => pure b
    | none => throw <| IO.userError s!"bad hex {h}"

end Tests
