import Tests.Support
import Bytes
import Backend

/-!
# Backend suite (unit W3.2, sub-unit 1a)

The 1a checks of `packages/crypto/backend/docs/PLAN.md`, "Test
milestones", over the OpenSSL shim:

* Ed25519: the four RFC 8032 §7.1 entries of `keys-rfc8032.json`. The
  derived public key and the signature match byte for byte, and a
  tampered message fails verification.
* ChaCha20-Poly1305: the RFC 8439 §2.8.2 vector, inline (the spike's
  shape). The seal matches, the open returns the plaintext, and a wrong
  AD, a wrong nonce, and a flipped tag bit each fail with `authFailed`.
* The three key types of `keys-go-libp2p.json`, through the raw key
  fields the extractor emits beside the envelopes. Each derives the
  fixture's public key, verifies the fixture's signature, and verifies
  a fresh signature of its own. The RSA re-sign is byte-identical
  (`sigDeterministic`). go-libp2p signs secp256k1 by RFC 6979, and so
  does the shim, so the secp256k1 re-sign is byte-identical too, and
  the digest signer gives the fixture's `(r, s)`. Sixteen more messages
  check that both forms agree, are low-S, and verify. P-256 signs with
  a random nonce. The secp256k1 fixture point passes
  `secp256k1PointValid`, and a point with an unknown prefix fails it.
* Random bytes: a draw returns the requested length, two draws differ,
  and a draw past the 1 MiB cap is `invalidInput`.
* One smoke call each for SHA-1, SHA-256 (interim), SHA-512, HMAC, and
  HKDF. The W3.3 cross-check closes them. SHA-1 also reproduces the
  multihash spec vector and the empty-input digest.

X25519 has no captured file. The Noise transcripts anchor it (W5.3).
The suite adds the RFC 7748 §6.1 key-agreement example as a named
fixed case, and the small-order rejection.
-/

set_option autoImplicit false

namespace Tests

open Bytes Backend

/-- A 32-byte key from hex. Any other size fails the run. -/
private def key32 (where_ hex : String) : IO Key32 := do
  match Key32.ofByteArray? (← unhex where_ hex) with
  | some k => pure k
  | none => throw <| IO.userError s!"{where_}: not 32 bytes: {hex}"

/-- The hex text of an `Except` answer, or the error's name. -/
private def hexOf {α : Type} (f : α → ByteArray) : Except CryptoError α → String
  | .ok b => toHex (f b)
  | .error e => s!"error {repr e}"

/-! ## ECDSA test helpers

Shared with `Tests.HazmatPins`. Test-side parsing only: the shim's own
DER handling is what the suites test, and these helpers read its output
and the fixtures. -/

namespace Ecdsa

/-- The big-endian number the bytes spell. -/
def natOfBytes (b : ByteArray) : Nat :=
  b.foldl (fun n x => n * 256 + x.toNat) 0

/-- `n` as `len` big-endian bytes; the high bytes past `len` drop. -/
def bytesOfNat (len n : Nat) : ByteArray :=
  ByteArray.mk ((List.range len).reverse.map fun i => ((n / 256 ^ i) % 256).toUInt8).toArray

/-- The two integers `(r, s)` of a DER `ECDSA-Sig-Value`, a SEQUENCE of
two INTEGERs with one-byte lengths, which every P-256 and secp256k1
signature has. A malformed signature fails the run. -/
def derSig (where_ : String) (sig : ByteArray) : IO (Nat × Nat) := do
  let int (at_ : Nat) : IO (Nat × Nat) := do
    unless sig.get! at_ == 0x02 do throw <| IO.userError s!"{where_}: not a DER INTEGER"
    let len := (sig.get! (at_ + 1)).toNat
    pure (natOfBytes (sig.extract (at_ + 2) (at_ + 2 + len)), at_ + 2 + len)
  unless sig.get! 0 == 0x30 do throw <| IO.userError s!"{where_}: not a DER SEQUENCE"
  let (r, next) ← int 2
  let (s, _) ← int next
  pure (r, s)

/-- The secp256k1 group order n (SEC 2 §2.4.1). -/
def secp256k1Order : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- The minimal DER INTEGER of a nonnegative `n` below 2^256: the
big-endian bytes without leading zeros. When the top bit of the first
byte is 1, one zero byte goes in front, so the value reads as positive
(X.690 §8.3). -/
def derInt (n : Nat) : ByteArray :=
  let raw := (bytesOfNat 32 n).toList.dropWhile (· == 0)
  let body := if raw.isEmpty then [0] else if raw.head! ≥ 0x80 then 0 :: raw else raw
  ByteArray.mk (#[0x02, body.length.toUInt8] ++ body.toArray)

/-- The DER `ECDSA-Sig-Value` of `(r, s)`. -/
def derSigOf (r s : Nat) : ByteArray :=
  let body := derInt r ++ derInt s
  ByteArray.mk #[0x30, body.size.toUInt8] ++ body

end Ecdsa

/-- `b` with the low bit of its first byte flipped. An empty `b` stays
empty. -/
private def tamper (b : ByteArray) : ByteArray :=
  if b.isEmpty then b else b.set! 0 (b.get! 0 ^^^ 1)

private def ed25519 (r : Runner) : IO Unit := do
  let file := "keys-rfc8032.json"
  let j ← loadJson file
  for v in ← jArr file j "ed25519" do
    let name ← jStr file v "name"
    let seed ← key32 file (← jStr file v "seedHex")
    let msg ← unhex file (← jStr file v "msgHex")
    let pub ← jStr file v "pubHex"
    let sig ← jStr file v "sigHex"
    r.check s!"Ed25519 {name}: public key" (hexOf Key32.bytes (ed25519PublicKey seed) == pub)
    r.check s!"Ed25519 {name}: signature" (hexOf id (ed25519Sign seed msg) == sig)
    let pubB ← unhex file pub
    let sigB ← unhex file sig
    r.check s!"Ed25519 {name}: verifies" (ed25519Verify pubB msg sigB)
    -- `tamper` cannot change an empty message, so the appended byte
    -- covers TEST 1.
    r.check s!"Ed25519 {name}: a tampered message fails"
      (!ed25519Verify pubB (msg.push 0) sigB && (msg.isEmpty || !ed25519Verify pubB (tamper msg) sigB))
    r.check s!"Ed25519 {name}: a short signature fails"
      (!ed25519Verify pubB msg (sigB.extract 0 63))

private def chacha (r : Runner) : IO Unit := do
  -- RFC 8439 §2.8.2: the AEAD test vector.
  let w := "RFC 8439 §2.8.2"
  let key ← key32 w "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  let some nonce := Nonce12.ofByteArray? (← unhex w "070000004041424344454647")
    | throw <| IO.userError s!"{w}: nonce"
  let some badNonce := Nonce12.ofByteArray? (← unhex w "070000004041424344454648")
    | throw <| IO.userError s!"{w}: nonce"
  let ad ← unhex w "50515253c0c1c2c3c4c5c6c7"
  let pt := ofString ("Ladies and Gentlemen of the class of '99: If I could offer you " ++
    "only one tip for the future, sunscreen would be it.")
  let sealed := "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6" ++
    "3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36" ++
    "92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc" ++
    "3ff4def08e4b7a9de576d26586cec64b6116" ++ "1ae10b594f09e26a7e902ecbd0600691"
  r.check "ChaCha20-Poly1305 RFC 8439 §2.8.2: seal" (hexOf id (chachaSeal key nonce ad pt) == sealed)
  let ct ← unhex w sealed
  r.check "ChaCha20-Poly1305 RFC 8439 §2.8.2: open" (succeedsWith pt (chachaOpen key nonce ad ct))
  r.check "ChaCha20-Poly1305: a wrong AD fails"
    (failsWith .authFailed (chachaOpen key nonce (tamper ad) ct))
  r.check "ChaCha20-Poly1305: a wrong nonce fails"
    (failsWith .authFailed (chachaOpen key badNonce ad ct))
  let flipped := ct.set! (ct.size - 1) (ct.get! (ct.size - 1) ^^^ 0x80)
  r.check "ChaCha20-Poly1305: a flipped tag bit fails"
    (failsWith .authFailed (chachaOpen key nonce ad flipped))
  r.check "ChaCha20-Poly1305: a message shorter than the tag fails"
    (failsWith .authFailed (chachaOpen key nonce ad (ct.extract 0 15)))
  r.check "ChaCha20-Poly1305: the empty plaintext round-trips"
    (match chachaSeal key nonce ad .empty with
     | .ok s => s.size == aeadTagLen && succeedsWith ByteArray.empty (chachaOpen key nonce ad s)
     | .error _ => false)

private def x25519Fixed (r : Runner) : IO Unit := do
  -- RFC 7748 §6.1: the Alice and Bob example.
  let w := "RFC 7748 §6.1"
  let alice ← key32 w "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
  let bob ← key32 w "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"
  let alicePub := "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a"
  let bobPub := "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f"
  let shared := "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742"
  r.check "X25519 RFC 7748 §6.1: Alice's public key" (hexOf Key32.bytes (x25519PublicKey alice) == alicePub)
  r.check "X25519 RFC 7748 §6.1: Bob's public key" (hexOf Key32.bytes (x25519PublicKey bob) == bobPub)
  r.check "X25519 RFC 7748 §6.1: Alice's shared secret"
    (hexOf Key32.bytes (x25519 alice (← key32 w bobPub)) == shared)
  r.check "X25519 RFC 7748 §6.1: Bob's shared secret"
    (hexOf Key32.bytes (x25519 bob (← key32 w alicePub)) == shared)
  -- The point 0 has small order: the shared secret is all zero.
  r.check "X25519: a small-order peer key is invalidKey"
    (match x25519 alice (← key32 w ("".pushn '0' 64)) with
     | .error .invalidKey => true
     | _ => false)

private def goKeys (r : Runner) : IO Unit := do
  let file := "keys-go-libp2p.json"
  let j ← loadJson file
  let msg ← unhex file (← jStr file j "messageHex")
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    let priv ← unhex file (← jStr file c "privRawHex")
    let pub ← unhex file (← jStr file c "pubRawHex")
    let sig ← unhex file (← jStr file c "sigHex")
    match name with
    | "rsa" =>
      r.check "go key rsa: derives the fixture public key" (succeedsWith pub (rsaPublicKey priv))
      r.check "go key rsa: the PKCS#1 re-encode gives the fixture bytes" (succeedsWith priv (rsaPkcs1 priv))
      r.check "go key rsa: verifies the fixture signature" (rsaVerify pub msg sig)
      r.check "go key rsa: the re-sign is byte-identical" (succeedsWith sig (rsaSign priv msg))
      r.check "go key rsa: a tampered message fails" (!rsaVerify pub (tamper msg) sig)
    | "secp256k1" =>
      let some scalar := Key32.ofByteArray? priv
        | throw <| IO.userError s!"{file}: secp256k1 scalar is not 32 bytes"
      r.check "go key secp256k1: derives the fixture public key"
        (succeedsWith pub (secp256k1PublicKey scalar))
      r.check "go key secp256k1: verifies the fixture signature" (secp256k1Verify pub msg sig)
      r.check "go key secp256k1: a tampered message fails" (!secp256k1Verify pub (tamper msg) sig)
      r.check "go key secp256k1: the fixture point is valid" (secp256k1PointValid pub)
      -- SEC 1 §2.3.3 knows the prefixes 0x02, 0x03, and 0x04 only.
      r.check "secp256k1: a point with prefix 0x05 is invalid"
        (!secp256k1PointValid (ByteArray.mk #[0x05] ++ pub.extract 1 pub.size))
      -- go-libp2p signs by RFC 6979 over SHA-256 (`sigDeterministic`),
      -- so both signers must give the fixture's (r, s) exactly.
      let digestOf (m : ByteArray) : IO Digest32 := do
        let some d := (sha256 m).toOption.bind Digest32.ofByteArray?
          | throw <| IO.userError s!"{file}: SHA-256 failed"
        pure d
      let digest ← digestOf msg
      let (fr, fs) ← Ecdsa.derSig file sig
      r.check "go key secp256k1: the re-sign is byte-identical" (succeedsWith sig (secp256k1Sign scalar msg))
      r.check "go key secp256k1: the digest signer gives the fixture (r, s)"
        (succeedsWith (Ecdsa.bytesOfNat 32 fr ++ Ecdsa.bytesOfNat 32 fs)
          (secp256k1SignDigest scalar digest))
      -- About half the raw signatures carry a high S, and the shim must
      -- replace S with n minus S. Sixteen messages reach that path with
      -- probability 1 minus 2^-16. Each DER answer must be low-S and
      -- verify, and the compact answer must hold the same (r, s).
      let draws := 16
      let mut good := 0
      for i in [0:draws] do
        let m := msg.push i.toUInt8
        if let (.ok der, .ok c) := (secp256k1Sign scalar m, secp256k1SignDigest scalar (← digestOf m)) then
          let (sr, ss) ← Ecdsa.derSig "secp256k1Sign" der
          if ss ≤ Ecdsa.secp256k1Order / 2 && secp256k1Verify pub m der &&
              c == Ecdsa.bytesOfNat 32 sr ++ Ecdsa.bytesOfNat 32 ss then
            good := good + 1
      r.check s!"secp256k1: {draws} signatures are low-S, verify, and agree in both forms ({good} did)"
        (good == draws)
      -- SEC 1 §3.2.1 takes a private key from [1, n - 1]. OpenSSL
      -- loads 0 and n and signs with them, so the shim checks the range.
      for (label, d) in [("zero", 0), ("the group order", Ecdsa.secp256k1Order)] do
        let some bad := Key32.ofByteArray? (Ecdsa.bytesOfNat 32 d)
          | throw <| IO.userError "a 32-byte scalar"
        r.check s!"secp256k1: every scalar binding rejects {label}"
          (failsWith .invalidKey (secp256k1PublicKey bad) &&
           failsWith .invalidKey (secp256k1Sign bad msg) &&
           failsWith .invalidKey (secp256k1SignDigest bad digest))
    | "ecdsa" =>
      r.check "go key ecdsa: derives the fixture public key" (succeedsWith pub (p256PublicKey priv))
      r.check "go key ecdsa: the SEC1 re-encode gives the fixture bytes" (succeedsWith priv (p256Sec1 priv))
      r.check "go key ecdsa: verifies the fixture signature" (p256Verify pub msg sig)
      r.check "go key ecdsa: a tampered message fails" (!p256Verify pub (tamper msg) sig)
      match ← (p256Sign priv msg).run with
      | .ok own => r.check "go key ecdsa: a fresh signature verifies" (p256Verify pub msg own)
      | .error e => r.check s!"go key ecdsa: sign failed with {repr e}" false
    | other => r.skip s!"go key {other}" "no binding for this key type"

private def random (r : Runner) : IO Unit := do
  let a ← (randomBytes 32).run
  let b ← (randomBytes 32).run
  r.check "random bytes: a draw has the requested length"
    (match a with | .ok x => x.size == 32 | .error _ => false)
  r.check "random bytes: two draws differ"
    (match a, b with | .ok x, .ok y => x != y | _, _ => false)
  r.check "random bytes: a zero-length draw is empty"
    (match ← (randomBytes 0).run with | .ok x => x.isEmpty | .error _ => false)
  r.check "random bytes: the 1 MiB cap is allowed"
    (match ← (randomBytes maxRandomBytes).run with
     | .ok x => x.size == maxRandomBytes | .error _ => false)
  r.check "random bytes: a draw past the 1 MiB cap is invalidInput"
    (failsWith .invalidInput (← (randomBytes (maxRandomBytes + 1)).run))

private def digests (r : Runner) : IO Unit := do
  let rfc := "hashes-rfc.json"
  let j ← loadJson rfc
  -- SHA-1: the multihash spec digest over "multihash" (the framing is
  -- two one-byte varints, the code and the length), and the
  -- well-known empty-input digest (FIPS 180-4).
  let mh := "multihash-examples.json"
  let mj ← loadJson mh
  for c in ← jArr mh mj "cases" do
    unless (← jStr mh c "algorithm") == "sha1" do continue
    let input := ofString (← jStr mh c "input")
    for e in ← jArr mh c "encodings" do
      unless (← jStr mh e "kind") == "hex" do continue
      let framed ← unhex mh (← jStr mh e "value")
      r.check "SHA-1 multihash spec digest" (succeedsWith (framed.extract 2 framed.size) (sha1 input))
  r.check "SHA-1 of the empty input"
    (hexOf id (sha1 .empty) == "da39a3ee5e6b4b0d3255bfef95601890afd80709")
  r.check "SHA-256 (interim) NIST abc"
    (hexOf id (sha256 (ofString "abc")) ==
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
  -- One entry each of the RFC files the pure pair owns.
  let some v512 := (← jArr rfc j "sha512").head? | throw <| IO.userError s!"{rfc}: sha512"
  r.check "SHA-512 smoke (FIPS 180-4 first example)"
    (hexOf id (sha512 (← unhex rfc (← jStr rfc v512 "inputHex"))) == (← jStr rfc v512 "digestHex"))
  let some hm := (← jArr rfc j "hmacSha256").head? | throw <| IO.userError s!"{rfc}: hmac"
  r.check "HMAC-SHA-256 smoke (RFC 4231 TC1)"
    (hexOf id (hmacSha256 (← unhex rfc (← jStr rfc hm "keyHex")) (← unhex rfc (← jStr rfc hm "dataHex")))
      == (← jStr rfc hm "macHex"))
  -- HMAC-SHA-256 with an empty key and an empty message.
  r.check "HMAC-SHA-256 with an empty key"
    (hexOf id (hmacSha256 .empty .empty) ==
      "b613679a0814d9ec772f95d778c35fc5ff1697c493715653c6c712144292c5ad")
  for v in ← jArr rfc j "hkdfSha256" do
    let name ← jStr rfc v "name"
    let okm ← jStr rfc v "okmHex"
    r.check s!"HKDF-SHA-256 smoke ({name})"
      (hexOf id (hkdfSha256 (← unhex rfc (← jStr rfc v "saltHex")) (← unhex rfc (← jStr rfc v "ikmHex"))
        (← unhex rfc (← jStr rfc v "infoHex")) (← jNat rfc v "l")) == okm)
  r.check "HKDF-SHA-256 at the 255-block limit gives 8160 bytes"
    (match hkdfSha256 .empty (ofString "k") .empty hkdfSha256MaxLen with
     | .ok b => b.size == hkdfSha256MaxLen | .error _ => false)
  r.check "HKDF-SHA-256 past the 255-block limit is invalidInput"
    (failsWith .invalidInput (hkdfSha256 .empty (ofString "k") .empty (hkdfSha256MaxLen + 1)))
  -- RFC 5869 §2.3 allows L = 0, and OpenSSL refuses it. The wrapper
  -- answers before the shim runs.
  r.check "HKDF-SHA-256 with a zero length gives the empty output"
    (succeedsWith ByteArray.empty (hkdfSha256 .empty (ofString "k") .empty 0))

def Backend.run (r : Runner) : IO Unit := do
  r.section "crypto/backend" "RFC 8032, RFC 8439, RFC 7748, go-libp2p core/crypto/test_data"
  ed25519 r
  chacha r
  x25519Fixed r
  goKeys r
  random r
  digests r

end Tests
