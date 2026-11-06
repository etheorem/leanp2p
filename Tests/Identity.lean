import Tests.Support
import Bytes
import Proto
import Libp2p.Identity

/-!
# Identity suite (unit W5.1)

The unit 1 milestones of `packages/libp2p/identity/docs/PLAN.md`, "Test
milestones":

* Marshal and unmarshal: the eight key protobufs of
  `keys-peer-ids.json` decode, re-encode to the same bytes, and carry
  the raw `Data` of the vector; each private key derives the public key
  of the same vector. The three go fixtures of `keys-go-libp2p.json`
  round-trip through both envelopes and derive their public key.
* Sign and verify through the facade, one case per key type. The RSA
  re-sign matches the go fixture byte for byte; secp256k1 and ECDSA
  verify (the backend pair records why). The RFC 8032 entries of
  `keys-rfc8032.json` sign through a 32-byte seed envelope.
* The strict rejections, each one concrete: a 31-byte Ed25519 public
  key, a 34-byte secp256k1 public key, key-type code 4, a 4-byte RSA
  `Data`, plus the Ed25519 private forms and the missing fields.
* Peer ids: the three string examples, the derived ids of the vector
  keys, the inlining boundary at 42 and 43 bytes, and the print-form
  round trip, base36 included.
* Marshal determinism: two marshals of one key are byte-identical, for
  every type.
-/

set_option autoImplicit false

namespace Tests

open Bytes Libp2p.Identity

/-- A value of an `Except`, or a failed run that names the error. -/
private def expectOk {α : Type} (where_ : String) : Except Error α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{where_}: {repr e}"

/-- The marshaled message of a key type and raw `Data`, through the
generic protobuf encoder, so a test can build any `Data` size. -/
private def keysBytes (t : KeyType) (d : ByteArray) : ByteArray :=
  match Keys.ofData? t d with
  | some k => Pb.encodeFieldsB k.toFields
  | none => .empty

/-- The input with its first byte flipped. -/
private def tamper (b : ByteArray) : ByteArray :=
  if h : 0 < b.size then b.set 0 (b[0] ^^^ 1) h else b

/-- `n` bytes that pass the DER shell: a SEQUENCE tag, then zeros. -/
private def derShellOf (n : Nat) : ByteArray :=
  ByteArray.mk (#[0x30] ++ Array.replicate (n - 1) 0)

/-! ## The spec key protobufs -/

private def specKeys (r : Runner) : IO Unit := do
  let file := "keys-peer-ids.json"
  let j ← loadJson file
  let mut pubs : List (String × PubKey) := []
  let mut privs : List (String × PrivKey) := []
  for v in ← jArr file j "keys" do
    let name ← jStr file v "name"
    let bytes ← unhex file (← jStr file v "bytesHex")
    let raw ← unhex file (← jStr file v "rawHex")
    -- The vector names end in "public key" or "private key"; the word
    -- before decides which unmarshal runs.
    let kind := (name.splitOn " ").reverse.drop 1 |>.head?
    match kind with
    | some "public" =>
      match PubKey.unmarshal? bytes with
      | .ok k =>
        r.check s!"spec {name}: decodes with the vector Data" (k.data == raw)
        r.check s!"spec {name}: re-encodes byte-exact" (k.marshal == bytes)
        r.check s!"spec {name}: a marshal of the re-decoded key is byte-identical"
          (succeedsWith k.marshal ((PubKey.unmarshal? k.marshal).map PubKey.marshal))
        r.check s!"spec {name}: the generic decoder agrees"
          (succeedsWith (k, bytes.size) (Pb.decodeMessageB? (α := PubKey) bytes))
        r.check s!"spec {name}: the generic encoder agrees" (Pb.encodeMessageB k == bytes)
        pubs := (name, k) :: pubs
      | .error e => r.check s!"spec {name}: decodes ({repr e})" false
    | some "private" =>
      match PrivKey.unmarshal? bytes with
      | .ok k =>
        r.check s!"spec {name}: decodes with the vector Data" (k.data == raw)
        r.check s!"spec {name}: re-encodes byte-exact" (k.marshal == bytes)
        r.check s!"spec {name}: a marshal of the re-decoded key is byte-identical"
          (succeedsWith k.marshal ((PrivKey.unmarshal? k.marshal).map PrivKey.marshal))
        r.check s!"spec {name}: the generic decoder agrees"
          (succeedsWith (k, bytes.size) (Pb.decodeMessageB? (α := PrivKey) bytes))
        r.check s!"spec {name}: the generic encoder agrees" (Pb.encodeMessageB k == bytes)
        privs := (name, k) :: privs
      | .error e => r.check s!"spec {name}: decodes ({repr e})" false
    | _ => r.skip s!"spec {name}" "not a key entry"
  -- Each private vector belongs to the public vector of the same type.
  for (name, priv) in privs do
    match pubs.find? (·.2.keyType == priv.keyType) with
    | some (_, pub) =>
      r.check s!"spec {name}: derives the public vector" (succeedsWith pub priv.toPublic)
    | none => r.check s!"spec {name}: has a public vector" false

/-! ## The go fixtures -/

private def goKeys (r : Runner) : IO Unit := do
  let file := "keys-go-libp2p.json"
  let j ← loadJson file
  let msg ← unhex file (← jStr file j "messageHex")
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    let privB ← unhex file (← jStr file c "privHex")
    let pubB ← unhex file (← jStr file c "pubHex")
    let sig ← unhex file (← jStr file c "sigHex")
    let priv ← expectOk s!"{file} {name} private" (PrivKey.unmarshal? privB)
    let pub ← expectOk s!"{file} {name} public" (PubKey.unmarshal? pubB)
    r.check s!"go key {name}: the private envelope round-trips" (priv.marshal == privB)
    r.check s!"go key {name}: the public envelope round-trips" (pub.marshal == pubB)
    r.check s!"go key {name}: derives the fixture public key" (succeedsWith pub priv.toPublic)
    r.check s!"go key {name}: verifies the fixture signature" (pub.verify msg sig)
    r.check s!"go key {name}: a tampered message fails" (!pub.verify (tamper msg) sig)
    match ← (priv.sign msg).run with
    | .ok own =>
      r.check s!"go key {name}: a fresh signature verifies" (pub.verify msg own)
      -- `sigDeterministic` holds for RSA here; the fixture also marks
      -- secp256k1, where OpenSSL draws a random nonce (the note of the
      -- fixture file), so only RSA compares bytes.
      if priv.keyType == .rsa then
        r.check s!"go key {name}: the re-sign is byte-identical" (own == sig)
    | .error e => r.check s!"go key {name}: signs ({repr e})" false

/-! ## Ed25519 through the seed envelope -/

private def rfc8032 (r : Runner) : IO Unit := do
  let file := "keys-rfc8032.json"
  let j ← loadJson file
  for v in ← jArr file j "ed25519" do
    let name ← jStr file v "name"
    let seed ← unhex file (← jStr file v "seedHex")
    let pubRaw ← unhex file (← jStr file v "pubHex")
    let msg ← unhex file (← jStr file v "msgHex")
    let sig ← unhex file (← jStr file v "sigHex")
    -- The 32-byte seed form: the unmarshal makes it the 64-byte envelope.
    let priv ← expectOk s!"{file} {name}" (PrivKey.unmarshal? (keysBytes .ed25519 seed))
    r.check s!"RFC 8032 {name}: the seed becomes the seed‖public envelope"
      (priv.data == seed ++ pubRaw)
    let pub ← expectOk s!"{file} {name}" priv.toPublic
    r.check s!"RFC 8032 {name}: derives the public key" (pub.data == pubRaw)
    match ← (priv.sign msg).run with
    | .ok own => r.check s!"RFC 8032 {name}: the signature matches" (own == sig)
    | .error e => r.check s!"RFC 8032 {name}: signs ({repr e})" false
    r.check s!"RFC 8032 {name}: the signature verifies" (pub.verify msg sig)
    r.check s!"RFC 8032 {name}: a tampered signature fails" (!pub.verify msg (tamper sig))

/-! ## Strict rejections -/

private def strict (r : Runner) : IO Unit := do
  let zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)
  -- The milestone cases.
  r.check "a 31-byte Ed25519 public Data fails"
    (failsWith (.keyData .ed25519 31) (PubKey.unmarshal? (keysBytes .ed25519 (zeros 31))))
  r.check "the generic decoder rejects a 31-byte Ed25519 public Data"
    (failsWith .badField
      (Pb.decodeMessageB? (α := PubKey) (keysBytes .ed25519 (zeros 31))))
  r.check "a 31-byte Ed25519 key derives no id"
    ((PubKey.unmarshal? (keysBytes .ed25519 (zeros 31)) >>= PeerId.ofPubKey) matches .error _)
  r.check "a 34-byte secp256k1 public Data fails"
    (failsWith (.keyData .secp256k1 34) (PubKey.unmarshal? (keysBytes .secp256k1 (zeros 34))))
  r.check "key-type code 4 fails in ofCode?" (KeyType.ofCode? 4 == none)
  r.check "a key type prints its schema name"
    ([KeyType.rsa, .ed25519, .secp256k1, .ecdsa].map toString == ["RSA", "Ed25519", "Secp256k1", "ECDSA"])
  -- `08 04 12 00`: Type 4, then an empty Data.
  r.check "key-type code 4 fails the unmarshal"
    (failsWith (.badKeyType 4) (PubKey.unmarshal? (ByteArray.mk #[8, 4, 18, 0])))
  r.check "a 4-byte RSA Data fails the DER shell"
    (failsWith (.keyData .rsa 4) (PubKey.unmarshal? (keysBytes .rsa (ByteArray.mk #[0x30, 2, 1, 0]))))
  -- The DER shell edges.
  r.check "a 7-byte DER shell fails"
    (failsWith (.keyData .ecdsa 7) (PubKey.ofData? .ecdsa (derShellOf 7)))
  r.check "an 8-byte DER shell passes" ((PubKey.ofData? .ecdsa (derShellOf 8)) matches .ok _)
  r.check "a DER key without the SEQUENCE tag fails"
    (failsWith (.keyData .rsa 8) (PubKey.ofData? .rsa (zeros 8)))
  -- The raw sizes on the private side.
  r.check "a 31-byte secp256k1 private Data fails"
    (failsWith (.keyData .secp256k1 31) (PrivKey.unmarshal? (keysBytes .secp256k1 (zeros 31))))
  r.check "a 63-byte Ed25519 private Data fails"
    (failsWith (.keyData .ed25519 63) (PrivKey.unmarshal? (keysBytes .ed25519 (zeros 63))))
  -- The missing fields: `08 01` alone has no Data, `12 00` alone no Type.
  r.check "a key with no Data fails"
    (failsWith (.missingField keysDataField) (PubKey.unmarshal? (ByteArray.mk #[8, 1])))
  r.check "a key with no Type fails"
    (failsWith (.missingField keysTypeField) (PubKey.unmarshal? (ByteArray.mk #[18, 0])))
  r.check "a cut protobuf fails as truncated"
    (failsWith (.message (.framing .truncated)) (PubKey.unmarshal? (ByteArray.mk #[8, 1, 18, 32, 0])))
  -- Unknown fields pass, and the marshal writes the canonical form.
  let file := "keys-peer-ids.json"
  let j ← loadJson file
  let edPub ← match (← jArr file j "keys").find? fun v =>
      (v.getObjValAs? String "name").toOption == some "ED25519 public key" with
    | some v => unhex file (← jStr file v "bytesHex")
    | none => throw <| IO.userError s!"{file}: no ED25519 public key"
  -- Field 3, VARINT 7: `18 07`.
  match PubKey.unmarshal? (edPub ++ ByteArray.mk #[0x18, 7]) with
  | .ok k => r.check "an unknown field passes, and the marshal drops it" (k.marshal == edPub)
  | .error e => r.check s!"an unknown field passes ({repr e})" false

/-! ## The Ed25519 private forms -/

private def ed25519Forms (r : Runner) : IO Unit := do
  let file := "keys-peer-ids.json"
  let j ← loadJson file
  let some v := (← jArr file j "keys").find? fun v =>
      (v.getObjValAs? String "name").toOption == some "ED25519 private key"
    | throw <| IO.userError s!"{file}: no ED25519 private key"
  let envelope ← unhex file (← jStr file v "rawHex")
  let pub := envelope.extract 32 64
  let legacy := envelope ++ pub
  match PrivKey.unmarshal? (keysBytes .ed25519 legacy) with
  | .ok k => r.check "the legacy 96-byte form becomes the 64-byte envelope" (k.data == envelope)
  | .error e => r.check s!"the legacy 96-byte form passes ({repr e})" false
  r.check "a legacy form with a different copy fails"
    (failsWith .publicMismatch (PrivKey.unmarshal? (keysBytes .ed25519 (envelope ++ tamper pub))))
  match PrivKey.unmarshal? (keysBytes .ed25519 (envelope.extract 0 32)) with
  | .ok k => r.check "the 32-byte seed becomes the vector envelope" (k.data == envelope)
  | .error e => r.check s!"the 32-byte seed passes ({repr e})" false
  -- A 64-byte envelope whose public half is not the seed's public key.
  r.check "an envelope with a foreign public half fails"
    (failsWith .publicMismatch
      (PrivKey.unmarshal? (keysBytes .ed25519 (envelope.extract 0 32 ++ tamper pub))))
  -- Marshal determinism across forms: one key entered as the seed, the
  -- envelope, and the legacy form marshals to one byte string.
  let forms := [envelope.extract 0 32, envelope, legacy].map fun d =>
    (PrivKey.unmarshal? (keysBytes .ed25519 d)).map PrivKey.marshal
  r.check "one Ed25519 key in three forms marshals to one byte string"
    (forms.all (succeedsWith (keysBytes .ed25519 envelope)))

/-! ## The PKCS#8 forms of the DER keys -/

/-- A DER length (X.690 §8.1.3): the short form below 128, then the long
form in one or two bytes, enough for the keys here. -/
private def derLen (n : Nat) : ByteArray :=
  if n < 0x80 then ByteArray.mk #[n.toUInt8]
  else if n < 0x100 then ByteArray.mk #[0x81, n.toUInt8]
  else ByteArray.mk #[0x82, (n / 256).toUInt8, (n % 256).toUInt8]

/-- The PKCS#8 `PrivateKeyInfo` around a type-specific key (RFC 5208 §5):
version 0, the algorithm identifier, then the key in an OCTET STRING. -/
private def pkcs8Of (algorithm key : ByteArray) : ByteArray :=
  let body := ByteArray.mk #[0x02, 0x01, 0x00] ++ algorithm ++
    ByteArray.mk #[0x04] ++ derLen key.size ++ key
  ByteArray.mk #[0x30] ++ derLen body.size ++ body

/-- `id-ecPublicKey` with the `prime256v1` curve (RFC 5480 §2.1.1). -/
private def ecAlgorithm : ByteArray := ByteArray.mk #[0x30, 0x13,
  0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01,
  0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]

/-- `rsaEncryption` with NULL parameters (RFC 8017 Appendix C). -/
private def rsaAlgorithm : ByteArray := ByteArray.mk #[0x30, 0x0d,
  0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01, 0x05, 0x00]

private def pkcs8 (r : Runner) : IO Unit := do
  let file := "keys-peer-ids.json"
  let j ← loadJson file
  let find (n k : String) : IO ByteArray := do
    match (← jArr file j "keys").find? fun v => (v.getObjValAs? String "name").toOption == some n with
    | some v => unhex file (← jStr file v k)
    | none => throw <| IO.userError s!"{file}: no {n}"
  let sec1 ← find "ECDSA private key" "rawHex"
  let sec1Message ← find "ECDSA private key" "bytesHex"
  let spki ← find "ECDSA public key" "rawHex"
  -- ECDSA: the table accepts PKCS#8 on import and holds the SEC1 form.
  match PrivKey.unmarshal? (keysBytes .ecdsa (pkcs8Of ecAlgorithm sec1)) with
  | .ok k =>
    r.check "ECDSA PKCS#8: the import derives the SEC1 key's public key"
      (succeedsWith spki (k.toPublic.map PubKey.data))
    r.check "ECDSA PKCS#8: the import marshals to the SEC1 vector bytes" (k.marshal == sec1Message)
  | .error e => r.check s!"ECDSA PKCS#8: the import passes ({repr e})" false
  -- RSA: the table holds PKCS#1 only, as go's `ParsePKCS1PrivateKey` reads.
  let pkcs1 ← find "rsa private key" "rawHex"
  let wrapped := pkcs8Of rsaAlgorithm pkcs1
  r.check "RSA PKCS#8: the import fails, since the table holds PKCS#1 only"
    (failsWith (.keyData .rsa wrapped.size) (PrivKey.unmarshal? (keysBytes .rsa wrapped)))

/-! ## Peer ids -/

private def peerIds (r : Runner) : IO Unit := do
  let file := "keys-peer-ids.json"
  let j ← loadJson file
  -- The three string examples parse, and print back in their form.
  let mut parsed : List (String × PeerId) := []
  for v in ← jArr file j "peerIdExamples" do
    let s ← jStr file v "string"
    match PeerId.ofString? s with
    | .ok p =>
      r.check s!"peer id {s}: prints back in its parsed form" (toString p == s)
      r.check s!"peer id {s}: the binary form round-trips"
        ((PeerId.ofBytes? p.toBytes).map (·.hash) |> succeedsWith p.hash)
      parsed := (s, p) :: parsed
    | .error e => r.check s!"peer id {s}: parses ({repr e})" false
  let get (s : String) : Option PeerId := (parsed.find? (·.1 == s)).map (·.2)
  let cidText := "bafzbeie5745rpv2m6tjyuugywy4d5ewrqgqqhfnf445he3omzpjbx5xqxe"
  let legacyText := "QmYyQSo1c1Ym7orWxLYvCrM2EmxFTANf8wXmmE7DWjhx5N"
  let edText := "12D3KooWD3eckifWpRn9wQpMG9R9hX3sD158z7EqHWmweQAJU5SA"
  match get cidText, get legacyText, get edText with
  | some c, some l, some e =>
    r.check "peer id: the CIDv1 and base58 texts of the spec share one multihash"
      (c.hash == l.hash)
    r.check "peer id: the derived == also compares the recorded form" (c != l)
    r.check "peer id: the CIDv1 id prints base58btc in that form"
      (c.toText? .base58 == some legacyText)
    r.check "peer id: the CIDv1 text prints from the base58 id"
      (l.toText? (.cid .base32) == some cidText)
    r.check "peer id: the sha256 examples are sha2-256 multihashes"
      (c.hash.code == .«sha2-256» && c.hash.digest.length == 32)
    r.check "peer id: the Ed25519 example inlines" (e.hash.code == .«identity»)
    -- base36, the other multibase the docs name.
    let b36 := (c.toText? (.cid .base36)).getD ""
    r.check s!"peer id: the base36 text {b36} parses to the same multihash"
      (succeedsWith c.hash ((PeerId.ofString? b36).map (·.hash)))
    r.check "peer id: the base36 text prints back"
      (succeedsWith b36 ((PeerId.ofString? b36).map toString))
    -- base32 decodes case-insensitively, and the print form is the
    -- canonical text of the recorded base, lower case.
    let mixed := "b" ++ (cidText.drop 1).toString.toUpper
    r.check "peer id: an upper-case base32 body parses to the same multihash"
      (succeedsWith c.hash ((PeerId.ofString? mixed).map (·.hash)))
    r.check "peer id: an upper-case base32 body prints in the canonical lower case"
      (succeedsWith cidText ((PeerId.ofString? mixed).map toString))
  | _, _, _ => r.check "peer id: the three examples parse" false
  -- Texts that are not peer ids.
  r.check "peer id: a CIDv1 under another codec fails"
    (failsWith (.peerIdCodec .badCid)
      (PeerId.ofString? "bafybeigdyrzt5sfp7udm7hu76uh7y26nf3efuylqabf3oclgtqy55fbzdi"))
  r.check "peer id: a sha2-256 digest of 31 bytes fails the shape"
    (failsWith .notPeerShape (PeerId.ofBytes? (ByteArray.mk (#[0x12, 31] ++ Array.replicate 31 0))))
  -- The peer id texts of nim and go: each accepted text names the id of
  -- its legacy text and prints back; each rejected text fails.
  for f in ["peerid-text-nim.json", "peerid-text-go.json"] do
    let jf ← loadJson f
    for v in ← jArr f jf "accepted" do
      let t ← jStr f v "text"
      let legacy ← jStr f v "legacy"
      r.check s!"{f} {t}: parses to the id of {legacy} and prints back"
        (match PeerId.ofString? t, PeerId.ofString? legacy with
          | .ok p, .ok q => p.hash == q.hash && toString p == t
          | _, _ => false)
    for v in ← jArr f jf "rejected" do
      let t ← jStr f v "text"
      r.check s!"{f} {repr t}: is no peer id" (PeerId.ofString? t |>.toOption |>.isNone)
  -- Proquint writes only an even number of bytes. A 37-byte key inlines
  -- to a 39-byte multihash, and its CIDv1 (`01 72` first) has 41 bytes,
  -- so the form has no text, and the id does not enter.
  let oddKey := ByteArray.mk (Array.replicate 37 0x41)
  if h : oddKey.size ≤ maxInlineKeyBytes then
    let p := PeerId.inline oddKey h
    r.check "peer id: a form with no text for the CID is badBaseValue"
      (failsWith (.peerIdCodec .badBaseValue) (PeerId.ofMultihash? p.hash (.cid .proquint)))
    r.check "peer id: the same id enters in base32"
      ((PeerId.ofMultihash? p.hash (.cid .base32)) matches .ok _)
  else r.check "peer id: the 37-byte key inlines" false
  -- The derived ids of the vector keys.
  for v in ← jArr file j "keys" do
    let name ← jStr file v "name"
    unless name.endsWith "public key" do continue
    let k ← expectOk s!"{file} {name}" (PubKey.unmarshal? (← unhex file (← jStr file v "bytesHex")))
    match PeerId.ofPubKey k with
    | .ok p =>
      let inlined := k.marshal.size ≤ maxInlineKeyBytes
      r.check s!"peer id of {name}: inlines exactly when the key is at most 42 bytes"
        ((p.hash.code == .«identity») == inlined)
      if k.keyType == .ed25519 then
        r.check s!"peer id of {name}: starts with 12D3KooW" (toString p |>.startsWith "12D3KooW")
      if k.keyType == .rsa then
        r.check s!"peer id of {name}: starts with Qm" (toString p |>.startsWith "Qm")
    | .error e => r.check s!"peer id of {name}: derives ({repr e})" false
  -- The inlining boundary: ECDSA keys with a DER-shell Data of 38 and 39
  -- bytes marshal to 42 and 43 bytes (`08 03 12 nn` plus the Data).
  for (n, inline) in [(38, true), (39, false)] do
    match PubKey.ofData? .ecdsa (derShellOf n) with
    | .ok k =>
      let size := k.marshal.size
      match PeerId.ofPubKey k with
      | .ok p =>
        r.check s!"peer id: a {size}-byte key {if inline then "inlines" else "hashes"}"
          (if inline then p.hash.code == .«identity» && p.hash.digest.length == size
           else p.hash.code == .«sha2-256» && p.hash.digest.length == 32)
      | .error e => r.check s!"peer id: a {size}-byte key derives ({repr e})" false
    | .error e => r.check s!"peer id: a {n}-byte DER shell passes ({repr e})" false

/-! ## The secp256k1 point forms -/

/-- The field prime of secp256k1 (SEC 2 §2.4.1). -/
private def k1Prime : Nat := 2 ^ 256 - 2 ^ 32 - 977

/-- `b ^ e % m` by squaring; test-only, over public values. -/
private def powMod (b e m : Nat) : Nat := Id.run do
  let mut acc := 1
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 = 1 then acc := acc * b % m
    b := b * b % m
    e := e / 2
  return acc

/-- The big-endian bytes of `n`, `k` of them. -/
private def beBytes (k n : Nat) : ByteArray :=
  ByteArray.mk ((List.range k).reverse.map fun i => (n / 256 ^ i % 256).toUInt8).toArray

/-- The uncompressed form of a compressed point: y is a square root of
x³ + 7, and p ≡ 3 (mod 4), so y = (x³ + 7) ^ ((p + 1) / 4); the tag
picks the parity. -/
private def decompress (c : ByteArray) : ByteArray :=
  let x := (c.extract 1 33).foldl (fun acc b => acc * 256 + b.toNat) 0
  let y0 := powMod ((x ^ 3 + 7) % k1Prime) ((k1Prime + 1) / 4) k1Prime
  -- The caller passes a 33-byte compressed point, so byte 0, the tag, exists.
  let y := if y0 % 2 == (c[0]!.toNat % 2) then y0 else k1Prime - y0
  ByteArray.mk #[0x04] ++ beBytes 32 x ++ beBytes 32 y

private def k1Forms (r : Runner) : IO Unit := do
  let file := "keys-peer-ids.json"
  let j ← loadJson file
  let some v := (← jArr file j "keys").find? fun v =>
      (v.getObjValAs? String "name").toOption == some "secp256k1 public key"
    | throw <| IO.userError s!"{file}: no secp256k1 public key"
  let compressed ← unhex file (← jStr file v "rawHex")
  -- The uncompressed form of the same point fails: the public `Data` is
  -- 33 bytes (owned contract 2).
  r.check "secp256k1: the 65-byte uncompressed form fails"
    (failsWith (.keyData .secp256k1 65)
      (PubKey.unmarshal? (keysBytes .secp256k1 (decompress compressed))))
  let badTag := ByteArray.mk #[0x04] ++ compressed.extract 1 33
  r.check "secp256k1: a 33-byte key with the tag 0x04 fails"
    (failsWith (.keyData .secp256k1 33) (PubKey.unmarshal? (keysBytes .secp256k1 badTag)))
  -- A compressed x with no point on the curve: x³ + 7 is no square, by
  -- Euler's criterion. The walk from the vector x ends within a few
  -- steps, since half of all x fail.
  let x0 := (compressed.extract 1 33).foldl (fun acc b => acc * 256 + b.toNat) 0
  let isSquare (x : Nat) : Bool := powMod ((x ^ 3 + 7) % k1Prime) ((k1Prime - 1) / 2) k1Prime ≤ 1
  let some xBad := (List.range 64).map (x0 + ·) |>.find? (!isSquare ·)
    | r.check "secp256k1: an x off the curve exists near the vector x" false
  let offCurve33 := ByteArray.mk #[0x02] ++ beBytes 32 xBad
  -- Owned contract 2: identity checks the point form, and the verifier
  -- behind the facade checks the point itself.
  match PubKey.unmarshal? (keysBytes .secp256k1 offCurve33) with
  | .ok k =>
    r.check "secp256k1: a compressed point off the curve verifies nothing"
      (!k.verify (ByteArray.mk #[0x61]) (ByteArray.mk (#[0x30, 6, 2, 1, 1, 2, 1, 1])))
  | .error e => r.check s!"secp256k1: an off-curve point passes the form check ({repr e})" false

def Identity.run (r : Runner) : IO Unit := do
  r.section "libp2p/identity" "peer-ids spec vectors, go-libp2p core/crypto/test_data, RFC 8032"
  specKeys r
  goKeys r
  rfc8032 r
  strict r
  ed25519Forms r
  pkcs8 r
  k1Forms r
  peerIds r

end Tests
