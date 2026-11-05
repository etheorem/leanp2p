import Tests.Support
import Libp2p.Identity
import Proto

/-!
# Key and peer-id suite

The key-type codes follow `vendor/specs/peer-ids/peer-ids.md`.
-/

set_option autoImplicit false

namespace Tests

open Libp2p.Identity

private def checkEnvelope {α : Type} [Pb.ProtoMessage α]
    (r : Runner) (name : String) (bytes : ByteArray) : IO Unit := do
  match Pb.decodeMessageB? (α := α) bytes with
  | .error e => r.check s!"key envelope decodes {name}: {repr e}" false
  | .ok (key, used) =>
      r.check s!"key envelope consumes input {name}" (used == bytes.size)
      r.check s!"key envelope preserves bytes {name}" (Pb.encodeMessageB key == bytes)
      match Pb.decodeMessage? (α := α) (Bytes.toNatList bytes) with
      | .error e => r.check s!"key model decodes {name}: {repr e}" false
      | .ok (modelKey, rest) =>
          r.check s!"key model agrees {name}"
            (rest.isEmpty && Pb.encodeMessage modelKey == Bytes.toNatList bytes)
          r.check s!"key envelope is deterministic across decoders {name}"
            (Pb.encodeMessageB key == Pb.encodeMessageB modelKey)

private def keyEnvelope (code : Nat) (raw : ByteArray) : IO ByteArray := do
  match Pb.Fields.ofList? [(1, .varint code), (2, .bytes (Bytes.toNatList raw))] with
  | .ok fs => pure (Pb.encodeFieldsB fs)
  | .error e => throw <| IO.userError s!"invalid key test fields: {repr e}"

private def isRejected {α : Type} [Pb.ProtoMessage α] (bytes : ByteArray) : Bool :=
  match Pb.decodeMessageB? (α := α) bytes with
  | .error _ => true
  | .ok _ => false

private def checkDerivation (r : Runner) (name : String) (key : PrivKey)
    (expected : ByteArray) : IO Unit := do
  match derivePubKey key with
  | .error error => r.check s!"public key derives {name}: {repr error}" false
  | .ok publicKey =>
      r.check s!"public key derives fixture {name}"
        (publicKey.keyType == key.keyType && publicKey.raw == expected)

-- Read fixture components independently of the production DER writer. This
-- helper only slices test data; no production decoder uses it.
private def derPayload? (bytes : ByteArray) (pos : Nat) : Option (ByteArray × Nat) := do
  let first ← bytes[pos + 1]?
  let (size, start) ← if first.toNat < 128 then
      some (first.toNat, pos + 2)
    else do
      let count := first.toNat - 128
      if count == 0 || pos + 2 + count > bytes.size then none
      else
        let mut size := 0
        for i in [:count] do
          size := size * 256 + (← bytes[pos + 2 + i]?).toNat
        some (size, pos + 2 + count)
  if start + size > bytes.size then none
  else some (bytes.extract start (start + size), start + size)

private def rsaPublicParts? (raw : ByteArray) : Option (ByteArray × ByteArray) := do
  let (spki, _) ← derPayload? raw 0
  let (_, next) ← derPayload? spki 0
  let (bits, _) ← derPayload? spki next
  let (rsa, _) ← derPayload? bits 1
  let (n, next) ← derPayload? rsa 0
  let (e, _) ← derPayload? rsa next
  pure (n, e)

private def rsaPrivateParts? (raw : ByteArray) : Option (Vector ByteArray 8) := do
  let (rsa, _) ← derPayload? raw 0
  let (_, start) ← derPayload? rsa 0
  let mut pos := start
  let mut components := #[]
  for _ in [:8] do
    let (component, next) ← derPayload? rsa pos
    components := components.push component
    pos := next
  if h : components.size = 8 then some ⟨components, h⟩ else none

private def checkPublic (r : Runner) (name : String) (bytes raw : ByteArray) : IO Unit := do
  match unmarshalPubKey? bytes with
  | .error e => r.check s!"public API decodes {name}: {repr e}" false
  | .ok key =>
      r.check s!"public API preserves Data {name}" (key.raw == raw)
      r.check s!"public API preserves encoding {name}" (marshalPubKey key == bytes)
      r.check s!"public construction and unmarshal encode identically {name}"
        ((PubKey.ofData? key.keyType raw).map marshalPubKey == some bytes)
      r.check s!"public backend Data {name}" (key.backendData == raw)
      match key.keyType with
      | .rsa =>
          let written := do
            let (n, e) ← rsaPublicParts? raw
            pure (Marshal.rsaPublicData n e)
          r.check s!"RSA SPKI writer matches fixture {name}" (written == some raw)
      | .ecdsa =>
          let point := raw.extract (raw.size - 64) raw.size
          r.check s!"P-256 SPKI writer matches fixture {name}"
            (Marshal.ecdsaPublicData (point.extract 0 32) (point.extract 32 64) == raw)
      | .secp256k1 =>
          r.check s!"SEC1 compressed writer matches fixture {name}"
            (Marshal.secp256k1PublicData (raw[0]! == 3) (raw.extract 1 raw.size) == raw)
      | .ed25519 => pure ()

private def checkPrivate (r : Runner) (name : String) (bytes raw : ByteArray) : IO Unit := do
  match unmarshalPrivKey? bytes with
  | .error e => r.check s!"private API decodes {name}: {repr e}" false
  | .ok key =>
      r.check s!"private API preserves Data {name}" (key.raw == raw)
      r.check s!"private API preserves encoding {name}" (marshalPrivKey key == bytes)
      r.check s!"private construction and unmarshal encode identically {name}"
        ((PrivKey.ofData? key.keyType raw).map marshalPrivKey == some bytes)
      let expected := if key.keyType == .ed25519 then raw.extract 0 32 else raw
      r.check s!"private backend Data {name}" (key.backendData == expected)
      match key.keyType with
      | .rsa =>
          r.check s!"RSA PKCS1 writer matches fixture {name}"
            ((rsaPrivateParts? raw).map Marshal.rsaPrivateData == some raw)
      | .ecdsa =>
          let written := do
            let (sec1, _) ← derPayload? raw 0
            let (_, next) ← derPayload? sec1 0
            let (scalar, _) ← derPayload? sec1 next
            let point := raw.extract (raw.size - 64) raw.size
            pure (Marshal.ecdsaPrivateData scalar (point.extract 0 32) (point.extract 32 64))
          r.check s!"P-256 SEC1 writer matches fixture {name}" (written == some raw)
      | .ed25519 =>
          r.check s!"Ed25519 private writer matches fixture {name}"
            (Marshal.ed25519PrivateData (raw.extract 0 32) (raw.extract 32 64) == raw)
      | .secp256k1 => pure ()

def Keys.run (r : Runner) : IO Unit := do
  r.section "key types" "libp2p/specs peer-ids.md: KeyType"
  for (code, keyType) in
      ([(0, .rsa), (1, .ed25519), (2, .secp256k1), (3, .ecdsa)] :
        List (Nat × KeyType)) do
    r.check s!"key type encodes as {code}" (keyType.toCode == code)
    r.check s!"key type decodes from {code}" (KeyType.ofCode? code == some keyType)
  r.check "key type rejects code 4" (KeyType.ofCode? 4 == none)

  let spec ← loadJson "keys-peer-ids.json"
  for entry in (← jArr "keys-peer-ids.json" spec "keys") do
    let name ← jStr "keys-peer-ids.json" entry "name"
    let bytes ← unhex name (← jStr "keys-peer-ids.json" entry "bytesHex")
    let raw ← unhex name (← jStr "keys-peer-ids.json" entry "rawHex")
    if name.endsWith "private key" then
      checkEnvelope (α := PrivKey) r name bytes
      checkPrivate r name bytes raw
    else
      checkEnvelope (α := PubKey) r name bytes
      checkPublic r name bytes raw

  let goKeys ← loadJson "keys-go-libp2p.json"
  for entry in (← jArr "keys-go-libp2p.json" goKeys "cases") do
    let name ← jStr "keys-go-libp2p.json" entry "name"
    checkEnvelope (α := PrivKey) r s!"go {name} private"
      (← unhex name (← jStr "keys-go-libp2p.json" entry "privHex"))
    checkEnvelope (α := PubKey) r s!"go {name} public"
      (← unhex name (← jStr "keys-go-libp2p.json" entry "pubHex"))
    checkPrivate r s!"go {name} private"
      (← unhex name (← jStr "keys-go-libp2p.json" entry "privHex"))
      (← unhex name (← jStr "keys-go-libp2p.json" entry "privRawHex"))
    checkPublic r s!"go {name} public"
      (← unhex name (← jStr "keys-go-libp2p.json" entry "pubHex"))
      (← unhex name (← jStr "keys-go-libp2p.json" entry "pubRawHex"))
    match unmarshalPrivKey? (← unhex name (← jStr "keys-go-libp2p.json" entry "privHex")) with
    | .error error => r.check s!"derivation fixture decodes {name}: {repr error}" false
    | .ok key =>
        checkDerivation r name key
          (← unhex name (← jStr "keys-go-libp2p.json" entry "pubRawHex"))

  let rfc ← loadJson "keys-rfc8032.json"
  for entry in (← jArr "keys-rfc8032.json" rfc "ed25519") do
    let name ← jStr "keys-rfc8032.json" entry "name"
    let seed ← unhex name (← jStr "keys-rfc8032.json" entry "seedHex")
    let publicKey ← unhex name (← jStr "keys-rfc8032.json" entry "pubHex")
    for raw in [seed, seed ++ publicKey, seed ++ publicKey ++ publicKey] do
      match PrivKey.ofData? .ed25519 raw with
      | none => r.check s!"RFC private key accepted {name}, length {raw.size}" false
      | some key => checkDerivation r s!"RFC {name}, length {raw.size}" key publicKey

  for (name, code, raw) in [
      ("31-byte Ed25519 public", 1, ByteArray.mk (Array.replicate 31 0)),
      ("34-byte secp256k1 public", 2, ByteArray.mk (Array.replicate 34 0)),
      ("unknown key type", 4, ByteArray.mk (Array.replicate 32 0)),
      ("four-byte RSA DER", 0, ByteArray.mk #[0x30, 0, 0, 0]),
      ("wrong ECDSA DER tag", 3, ByteArray.mk (Array.replicate 8 0))] do
    r.check s!"key rejects {name}" (isRejected (α := PubKey) (← keyEnvelope code raw))

  let seed := ByteArray.mk (Array.replicate 32 1)
  let pubBytes := ByteArray.mk (Array.replicate 32 2)
  for raw in [seed, seed ++ pubBytes, seed ++ pubBytes ++ pubBytes] do
    r.check s!"Ed25519 accepts private length {raw.size}"
      (PrivKey.ofData? .ed25519 raw).isSome
  r.check "Ed25519 rejects mismatched legacy public copies"
    (PrivKey.ofData? .ed25519 (seed ++ pubBytes ++ seed)).isNone
  r.check "Ed25519 rejects private length 63"
    (PrivKey.ofData? .ed25519 (ByteArray.mk (Array.replicate 63 0))).isNone
  r.check "secp256k1 rejects private length 31"
    (PrivKey.ofData? .secp256k1 (ByteArray.mk (Array.replicate 31 0))).isNone
  r.check "private RSA rejects short DER"
    (PrivKey.ofData? .rsa (ByteArray.mk #[0x30, 0, 0, 0])).isNone

  r.check "public envelope requires Type"
    (isRejected (α := PubKey) (Bytes.ofNatList ([0x12, 32] ++ List.replicate 32 0)))
  r.check "private envelope requires Data"
    (isRejected (α := PrivKey) (ByteArray.mk #[0x08, 1]))

  r.section "key Data writers" "peer-ids.md: per-type Data forms"
  r.check "Ed25519 writer concatenates seed and public key"
    (Marshal.ed25519PrivateData seed pubBytes == seed ++ pubBytes)
  r.check "secp256k1 writer emits compressed point prefix"
    (Marshal.secp256k1PublicData true pubBytes == ByteArray.mk #[3] ++ pubBytes)
  -- Small integers exercise DER layout, not RSA cryptographic validity.
  r.check "RSA public writer emits SPKI with unsigned INTEGER padding"
    (Marshal.rsaPublicData (ByteArray.mk #[0, 0x80]) (ByteArray.mk #[3]) ==
      (← unhex "RSA SPKI" "301b300d06092a864886f70d0101010500030a00300702020080020103"))
  r.check "RSA private writer emits PKCS#1"
    (Marshal.rsaPrivateData ⟨#[ByteArray.mk #[1], ByteArray.mk #[2], ByteArray.mk #[3],
        ByteArray.mk #[4], ByteArray.mk #[5], ByteArray.mk #[6], ByteArray.mk #[7],
        ByteArray.mk #[8]], by decide⟩ ==
      (← unhex "RSA PKCS1" "301b020100020101020102020103020104020105020106020107020108"))
  r.check "P-256 public writer emits SPKI"
    (Marshal.ecdsaPublicData seed pubBytes ==
      (← unhex "P256 SPKI head" "3059301306072a8648ce3d020106082a8648ce3d03010703420004") ++
        seed ++ pubBytes)
  r.check "P-256 private writer emits SEC1"
    (Marshal.ecdsaPrivateData seed seed pubBytes ==
      (← unhex "P256 SEC1 head" "30770201010420") ++ seed ++
        (← unhex "P256 SEC1 parameters" "a00a06082a8648ce3d030107a14403420004") ++
        seed ++ pubBytes)
  for (name, bytes) in [
      ("truncated Type", ByteArray.mk #[8]),
      ("truncated Data", ByteArray.mk #[8, 1, 18, 32, 0]),
      ("wrong Type wire kind", ByteArray.mk #[10, 1, 1, 18, 32] ++ seed),
      ("trailing malformed tag", ByteArray.mk #[8, 1, 18, 32] ++ seed ++ ByteArray.mk #[0])] do
    r.check s!"public unmarshal rejects {name}"
      (match unmarshalPubKey? bytes with | .error _ => true | .ok _ => false)
    r.check s!"private unmarshal rejects {name}"
      (match unmarshalPrivKey? bytes with | .error _ => true | .ok _ => false)

end Tests
