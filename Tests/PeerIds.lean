import Tests.Support
import Libp2p.Identity
import Multiformats

/-!
# Peer-id integration

The specification examples exercise the real multihash, CID, and multibase
codecs. The boundary cases check the complete key protobuf, including its
Type and Data fields, rather than the raw key length.
-/

set_option autoImplicit false

namespace Tests.PeerIds

open Libp2p.Identity Multiformats

private def rejected {α : Type} : Except Libp2p.Identity.Error α → Bool
  | .error _ => true
  | .ok _ => false

private def checkText (r : Runner) (text : String) : IO Unit := do
  match PeerId.ofString? text with
  | .error error => r.check s!"peer id parses {text}: {repr error}" false
  | .ok peer =>
      r.check s!"peer id preserves text {text}" (toString peer == text)
      match PeerId.ofBytes? peer.toBytes with
      | .error error => r.check s!"peer id parses binary {text}: {repr error}" false
      | .ok binary =>
          r.check s!"peer id binary preserves identity {text}" (binary == peer)
          r.check s!"peer id hash ignores text {text}" (hash binary == hash peer)
          r.check s!"peer id ordering ignores text {text}" (compare binary peer == .eq)
      match PeerId.ofString? peer.toCidString with
      | .error error => r.check s!"peer id converts to CID {text}: {repr error}" false
      | .ok cid => r.check s!"peer id CID preserves identity {text}" (cid == peer)

def run (r : Runner) : IO Unit := do
  r.section "peer ids" "libp2p/specs peer-ids.md; keys-peer-ids.json"
  let spec ← loadJson "keys-peer-ids.json"
  for entry in (← jArr "keys-peer-ids.json" spec "peerIdExamples") do
    checkText r (← jStr "keys-peer-ids.json" entry "string")
  -- The first two specification examples encode the same SHA-256 multihash.
  let expectedHash ← unhex "specification peer id"
    "12209dff3b17d74cf4d38a50d8b6383e92d181a10395a5e73a726dcccbd21bf6f0b9"
  for text in ["bafzbeie5745rpv2m6tjyuugywy4d5ewrqgqqhfnf445he3omzpjbx5xqxe",
      "QmYyQSo1c1Ym7orWxLYvCrM2EmxFTANf8wXmmE7DWjhx5N"] do
    match PeerId.ofString? text with
    | .error error => r.check s!"specification peer parses: {repr error}" false
    | .ok peer =>
        r.check "specification peer decodes the expected multihash"
          (peer.toBytes == expectedHash)

  -- The decoder accepts mixed case within a case-insensitive alphabet.
  -- Recording only the base would lose this exact accepted spelling.
  checkText r "bAfzbeie5745rpv2m6tjyuugywy4d5ewrqgqqhfnf445he3omzpjbx5xqxe"
  for entry in (← jArr "keys-peer-ids.json" spec "keys") do
    let name ← jStr "keys-peer-ids.json" entry "name"
    if !name.endsWith "private key" then
      let bytes ← unhex name (← jStr "keys-peer-ids.json" entry "bytesHex")
      match unmarshalPubKey? bytes with
      | .error error => r.check s!"peer id fixture key {name}: {repr error}" false
      | .ok key =>
          match PeerId.ofPublicKey key with
          | .error error => r.check s!"peer id derives {name}: {repr error}" false
          | .ok peer =>
              -- SHA-256 values were calculated independently with .NET's
              -- SHA256.HashData over the fixture's complete protobuf bytes.
              let expected := match key.keyType with
                | .rsa => "1220b6c8a8c0a3105fc27afca4fb1173791f038e4343fd56b7c67b616dbc30a04ccd"
                | .ecdsa => "122068362c312e155f4f7290b67f5cd094a22a0a4fbf20efd8c287934419350d36f7"
                | .ed25519 => "0024080112201ed1e8fae2c4a144b8be8fd4b47bf3d3b34b871c3cacf6010f0e42d474fce27e"
                | .secp256k1 => "002508021221037777e994e452c21604f91de093ce415f5432f701dd8cd1a7a6fea0e630bfca99"
              r.check s!"peer id derives fixture {name}"
                (peer.toBytes == (← unhex name expected))

  -- These buffers exercise the documented DER shell check, not RSA key
  -- validity. Peer-id derivation hashes the envelope without verifying it.
  for (rawSize, code) in [(38, HashCode.identity), (39, HashCode.«sha2-256»)] do
    let raw := ByteArray.mk (#[0x30] ++ Array.replicate (rawSize - 1) 0)
    match PubKey.ofData? .rsa raw with
    | .error _ => r.check s!"boundary key is accepted {rawSize}" false
    | .ok key =>
        r.check s!"boundary envelope size {rawSize}" ((marshalPubKey key).size == rawSize + 4)
        match PeerId.ofPublicKey key with
        | .error error => r.check s!"boundary derives {rawSize}: {repr error}" false
        | .ok peer =>
            r.check s!"boundary selects hash {rawSize}" (peer.multihash.code == code)
            if rawSize == 38 then
              r.check "42-byte envelope inlines every byte"
                (peer.toBytes == Bytes.ofNatList ([0, 42, 8, 0, 18, 38, 48] ++ List.replicate 37 0))
            else
              r.check "43-byte envelope hashes the complete protobuf"
                (peer.toBytes == (← unhex "43-byte envelope SHA-256"
                  "12209c2085358138d678f7c422e6bd05c0e89a0d83f836c41c75bd6b4ff7b1d424f7"))

  for (name, bytes) in [
      ("short SHA-256 digest", Bytes.ofNatList ([18, 31] ++ List.replicate 31 0)),
      ("SHA-512 digest", Bytes.ofNatList ([19, 64] ++ List.replicate 64 0)),
      ("trailing byte", Bytes.ofNatList ([18, 32] ++ List.replicate 33 0)),
      ("truncated digest", Bytes.ofNatList [18, 32, 0])] do
    r.check s!"peer id rejects {name}" (rejected (PeerId.ofBytes? bytes))
  r.check "peer id rejects empty text"
    (failsWith (.encoding .unknownBase) (PeerId.ofString? ""))
  r.check "peer id rejects overlong text"
    (failsWith .textTooLong (PeerId.ofString? (String.ofList (List.replicate 4097 '1'))))

  let digest := Bytes.ofNatList (List.replicate 32 0)
  let wrongCodec := Bytes.ofNatList ([1, 0x70, 18, 32] ++ List.replicate 32 0)
  r.check "peer id rejects CID with dag-pb codec"
    (failsWith .invalidCid (PeerId.ofString? (Multibase.encodeBase32 wrongCodec)))
  r.check "peer id rejects multibase-wrapped CIDv0"
    (failsWith .invalidCid
      (PeerId.ofString? (Multibase.encodeBase32 (Bytes.ofNatList [18, 32] ++ digest))))
  match PeerId.ofBytes? (Bytes.ofNatList [0, 1, 0]) with
  | .error error => r.check s!"odd CID fixture: {repr error}" false
  | .ok peer =>
      r.check "explicit Proquint conversion reports its odd-byte domain error"
        (failsWith (.encoding .badBaseValue) (peer.toCidString? .proquint))
  match PeerId.ofBytes? (Bytes.ofNatList [18, 32] ++ digest) with
  | .error error => r.check s!"SHA-256 fixture: {repr error}" false
  | .ok peer =>
      match PeerId.ofBytes? (Bytes.ofNatList [0, 32] ++ digest) with
      | .error error => r.check s!"identity fixture: {repr error}" false
      | .ok identity =>
          r.check "different hash codes identify different peers" (!(peer == identity))
          r.check "peer ordering distinguishes hash codes" (compare identity peer == .lt)
      for base in Multibase.Base.all do
        match peer.toCidString? base with
        | .error error => r.check s!"CID base {repr base}: {repr error}" false
        | .ok text =>
            r.check s!"CID base recovers the source peer {repr base}"
              (succeedsWith peer (PeerId.ofString? text))
            checkText r text

end Tests.PeerIds
