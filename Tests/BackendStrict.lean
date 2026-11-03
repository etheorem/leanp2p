import Tests.Support
import Tests.Backend
import Bytes
import Backend

/-!
# Backend strictness suite (unit W3.2, sub-unit 1b)

The 1b milestones of `packages/crypto/backend/docs/PLAN.md` other than
X.509 (`Tests.BackendX509`) and the soak (`Tests.BackendSoak`).

**Verifier strictness, one regression per rule of root §4.6.** Each of
these fails:
- a P-256 key under the RSA verifier, and an RSA signature under the
  P-256 verifier (the go fixtures of `keys-go-libp2p.json`)
- a compressed and a hybrid P-256 key
- a 1024-bit and a 9216-bit RSA key, at every entry point (generated
  fixtures)
- a high-S secp256k1 signature, built from a fresh low-S one by
  replacing S with n minus S
- a secp256k1 key under the P-256 verifier

The X.509 rules live in `Tests.BackendX509`.

**Determinism.** Ed25519 signing, RSA signing, and a ChaCha20-Poly1305
seal give the same bytes twice. The two ECDSA signers give different
signatures on two draws, and both verify.

**Key generation.** A fresh key of each type derives its public key and
passes a sign and verify round trip. Two fresh X25519 keys agree on the
shared secret. An RSA size outside 2048 to 8192 bits is
`invalidInput`.
-/

set_option autoImplicit false

namespace Tests

-- Inside `namespace Tests`, a bare `Backend` names the suite namespace
-- `Tests.Backend`. `_root_.Backend` names the library.
open Bytes _root_.Backend

/-- The `ok` value of an IO computation, or a failed check and `none`. -/
private def okOr {α : Type} (r : Runner) (name : String) (x : ExceptT CryptoError IO α) :
    IO (Option α) := do
  match ← x.run with
  | .ok a => pure (some a)
  | .error e => r.check s!"{name}: failed with {repr e}" false; pure none

private def strictness (r : Runner) : IO Unit := do
  -- Cross-type: the go fixtures, each fed to the other family's verifier.
  let go := "keys-go-libp2p.json"
  let gj ← loadJson go
  let msg ← unhex go (← jStr go gj "messageHex")
  let cases ← jArr go gj "cases"
  let field (name key : String) : IO ByteArray := do
    let some c ← cases.findM? (fun c => return (← jStr go c "name") == name)
      | throw <| IO.userError s!"{go}: no {name} case"
    unhex go (← jStr go c key)
  let rsaPub ← field "rsa" "pubRawHex"
  let rsaSig ← field "rsa" "sigHex"
  let ecPub ← field "ecdsa" "pubRawHex"
  let ecSig ← field "ecdsa" "sigHex"
  r.check "strictness: a P-256 key under the RSA verifier fails" (!rsaVerify ecPub msg ecSig)
  r.check "strictness: an RSA signature under the P-256 verifier fails" (!p256Verify rsaPub msg rsaSig)
  r.check "strictness: the controls verify under their own verifiers"
    (rsaVerify rsaPub msg rsaSig && p256Verify ecPub msg ecSig)
  -- The point forms OpenSSL loads and Go rejects: compressed (a 59-byte
  -- SPKI, tag 0x02 or 0x03 by the parity of y, then x) and hybrid (the
  -- uncompressed layout with tag 0x06 or 0x07).
  let parity := ecPub.get! (ecPub.size - 1) &&& 1
  let compressed := (ecPub.extract 0 26).set! 1 0x39 |>.set! 24 0x22
    |>.push (0x02 ||| parity) |>.append (ecPub.extract 27 59)
  r.check "strictness: a compressed P-256 key fails" (!p256Verify compressed msg ecSig)
  r.check "strictness: a hybrid P-256 key fails" (!p256Verify (ecPub.set! 26 (0x06 ||| parity)) msg ecSig)

  -- RSA sizes: the generated 1024-bit and 9216-bit keys.
  let fx := "backend-strictness.json"
  let fj ← loadFixture fx
  let fmsg ← unhex fx (← jStr fx fj "messageHex")
  for k in ← jArr fx fj "rsaOutOfRange" do
    let bits ← jNat fx k "bits"
    let priv ← unhex fx (← jStr fx k "privHex")
    let spki ← unhex fx (← jStr fx k "spkiHex")
    let sig ← unhex fx (← jStr fx k "sigHex")
    r.check s!"strictness: a {bits}-bit RSA key fails verification" (!rsaVerify spki fmsg sig)
    r.check s!"strictness: a {bits}-bit RSA key does not derive" (failsWith .invalidKey (rsaPublicKey priv))
    r.check s!"strictness: a {bits}-bit RSA key does not sign" (failsWith .invalidKey (rsaSign priv fmsg))

  -- A SEC1 P-256 key that stores its public point compressed: the
  -- derivation still gives the uncompressed SPKI the verifiers take.
  let cpriv ← unhex fx (← jStr fx fj "p256CompressedSec1Hex")
  match p256PublicKey cpriv, ← (p256Sign cpriv fmsg).run with
  | .ok spki, .ok sig =>
    r.check "strictness: a compressed-point SEC1 key derives the 91-byte uncompressed SPKI"
      (p256SpkiUncompressed spki)
    r.check "strictness: a compressed-point SEC1 key signs, and the signature verifies"
      (p256Verify spki fmsg sig)
  | _, _ => r.check "strictness: a compressed-point SEC1 key derives and signs" false

  -- A secp256k1 key under the P-256 verifier.
  let k1 ← jObj fx fj "secp256k1Spki"
  r.check "strictness: a secp256k1 SPKI key under the P-256 verifier fails"
    (!p256Verify (← unhex fx (← jStr fx k1 "spkiHex")) fmsg (← unhex fx (← jStr fx k1 "sigHex")))

  -- High S: a fresh low-S signature, then its twin with S replaced by
  -- n minus S.
  let some scalar ← okOr r "strictness: secp256k1 generate" secp256k1Generate | return
  let some point := (secp256k1PublicKey scalar).toOption
    | r.check "strictness: secp256k1 derive" false
  let some low ← okOr r "strictness: secp256k1 sign" (secp256k1Sign scalar msg) | return
  let (sr, ss) ← Ecdsa.derSig "secp256k1Sign" low
  let high := Ecdsa.derSigOf sr (Ecdsa.secp256k1Order - ss)
  r.check "strictness: the low-S control verifies" (secp256k1Verify point msg low)
  r.check "strictness: the high-S twin re-encodes as DER" (Ecdsa.derSigOf sr ss == low)
  r.check "strictness: a high-S secp256k1 signature fails" (!secp256k1Verify point msg high)

private def determinism (r : Runner) : IO Unit := do
  let msg := ofString "determinism"
  let some seed ← okOr r "determinism: ed25519 generate" ed25519Generate | return
  r.check "determinism: Ed25519 signs the same bytes twice"
    (match ed25519Sign seed msg, ed25519Sign seed msg with
     | .ok a, .ok b => a == b | _, _ => false)
  let some rsaPriv ← okOr r "determinism: rsa generate" (rsaGenerate 2048) | return
  r.check "determinism: RSA PKCS#1 v1.5 signs the same bytes twice"
    (match rsaSign rsaPriv msg, rsaSign rsaPriv msg with
     | .ok a, .ok b => a == b | _, _ => false)
  let some key ← okOr r "determinism: chacha key" x25519Generate | return
  let some nonce := Nonce12.ofByteArray? (ByteArray.mk (Array.replicate 12 7))
    | r.check "determinism: nonce" false
  r.check "determinism: a ChaCha20-Poly1305 seal gives the same bytes twice"
    (match chachaSeal key nonce .empty msg, chachaSeal key nonce .empty msg with
     | .ok a, .ok b => a == b | _, _ => false)
  -- The randomized signers: two draws differ, and both verify.
  let some p256Priv ← okOr r "determinism: p256 generate" p256Generate | return
  let some p256Pub := (p256PublicKey p256Priv).toOption | r.check "determinism: p256 derive" false
  let some a ← okOr r "determinism: p256 sign" (p256Sign p256Priv msg) | return
  let some b ← okOr r "determinism: p256 sign" (p256Sign p256Priv msg) | return
  r.check "determinism: two P-256 signatures differ, and both verify"
    (a != b && p256Verify p256Pub msg a && p256Verify p256Pub msg b)
  let some k1 ← okOr r "determinism: secp256k1 generate" secp256k1Generate | return
  let some k1Pub := (secp256k1PublicKey k1).toOption | r.check "determinism: secp256k1 derive" false
  let some c ← okOr r "determinism: secp256k1 sign" (secp256k1Sign k1 msg) | return
  let some d ← okOr r "determinism: secp256k1 sign" (secp256k1Sign k1 msg) | return
  r.check "determinism: two secp256k1 signatures differ, and both verify"
    (c != d && secp256k1Verify k1Pub msg c && secp256k1Verify k1Pub msg d)

private def keyGeneration (r : Runner) : IO Unit := do
  let msg := ofString "key generation"
  -- Ed25519.
  if let some seed ← okOr r "keygen: Ed25519" ed25519Generate then
    r.check "keygen: a fresh Ed25519 key derives, signs, and verifies"
      (match ed25519PublicKey seed, ed25519Sign seed msg with
       | .ok pub, .ok sig => ed25519Verify pub.bytes msg sig
       | _, _ => false)
  -- X25519: two fresh keys agree.
  if let (some a, some b) := (← okOr r "keygen: X25519" x25519Generate,
      ← okOr r "keygen: X25519" x25519Generate) then
    r.check "keygen: two fresh X25519 keys agree on the shared secret"
      (match x25519PublicKey a, x25519PublicKey b with
       | .ok pa, .ok pb =>
         match x25519 a pb, x25519 b pa with
         | .ok s1, .ok s2 => s1 == s2 && a != b
         | _, _ => false
       | _, _ => false)
  -- secp256k1.
  if let some k ← okOr r "keygen: secp256k1" secp256k1Generate then
    if let some sig ← okOr r "keygen: secp256k1 sign" (secp256k1Sign k msg) then
      r.check "keygen: a fresh secp256k1 key derives, signs, and verifies"
        (match secp256k1PublicKey k with
         | .ok pub => pub.size == 33 && secp256k1Verify pub msg sig
         | .error _ => false)
  -- ECDSA P-256.
  if let some k ← okOr r "keygen: P-256" p256Generate then
    if let some sig ← okOr r "keygen: P-256 sign" (p256Sign k msg) then
      r.check "keygen: a fresh P-256 key derives, signs, and verifies"
        (match p256PublicKey k with
         | .ok pub => p256Verify pub msg sig
         | .error _ => false)
  -- RSA, at the lower bound.
  if let some k ← okOr r "keygen: RSA" (rsaGenerate rsaMinBits) then
    r.check "keygen: a fresh 2048-bit RSA key derives, signs, and verifies"
      (match rsaPublicKey k, rsaSign k msg with
       | .ok pub, .ok sig => rsaVerify pub msg sig
       | _, _ => false)
  r.check "keygen: a 1024-bit RSA request is invalidInput"
    (failsWith .invalidInput (← (rsaGenerate 1024).run))
  r.check "keygen: a 9216-bit RSA request is invalidInput"
    (failsWith .invalidInput (← (rsaGenerate 9216).run))

def BackendStrict.run (r : Runner) : IO Unit := do
  r.section "crypto/backend strictness" "root ARCHITECTURE §4.6; go-libp2p core/crypto/test_data; generated fixtures"
  strictness r
  determinism r
  keyGeneration r

end Tests
