import Tests.Support
import Bytes
import Backend

/-!
# Backend X.509 suite (unit W3.2, sub-unit 1b)

The X.509 checks of `packages/crypto/backend/docs/PLAN.md`, milestones
for 1b.

**`tls-ext.json`, the four certificates of the TLS spec (tls.md, "Test
vectors").** All four parse with the key extension
`1.3.6.1.4.1.53594.1.1`, pass the self-signature check, and give the
validity times their DER fields encode: NotBefore `750101130000Z`
(UTCTime, 1975-01-01 13:00:00 UTC, 157813200) and NotAfter
`40960101130000Z` (GeneralizedTime, 4096-01-01 13:00:00 UTC,
67090165200). The file carries no expected times, so the literals here
come from those fields.

Certificate 4 is invalid in a way X.509 cannot see: it is a well-formed
self-signed certificate, and the host-key signature inside the
extension does not verify. Checking that needs the extension's
`SignedKey` structure, the key protobuf, and the signing prefix, all
knowledge above the backend. The suite composes the backend helpers the
way the TLS handshake will (root §8 defers that layer): it reads the
`SignedKey`, picks the verifier by the key type, and checks the
signature over `libp2p-tls-handshake:` and the certificate's SPKI.
Certificates 1 to 3 pass; certificate 4 fails.

**`Tests/fixtures/backend-strictness.json`, generated certificates.**
Each breaks one rule (`scripts/gen-backend-fixtures.py`): an unknown
critical extension, a missing required extension, and an extension that
appears twice are rejected; a critical required extension, a critical
`basicConstraints`, and an unknown non-critical extension are accepted;
an expired certificate parses, and `validAt` rejects it against a
literal time; a SHA-1 signature and a 1024-bit RSA key parse and fail
the self-signature check. The comparison is pure; the production caller
owns the clock.
-/

set_option autoImplicit false

namespace Tests

open Bytes Backend

private def unhexX (where_ hex : String) : IO ByteArray :=
  match ofHex? hex with
  | some b => pure b
  | none => throw <| IO.userError s!"{where_}: no hex text: {hex}"

/-- One DER element at `at_`: its tag and the bounds of its contents.
Short lengths and the one- and two-byte long forms (X.690 §8.1.3); the
spec certificates need no more. -/
private def tlv (where_ : String) (b : ByteArray) (at_ : Nat) : IO (UInt8 × Nat × Nat) := do
  let l0 := (b.get! (at_ + 1)).toNat
  let (len, start) :=
    if l0 < 0x80 then (l0, at_ + 2)
    else if l0 == 0x81 then ((b.get! (at_ + 2)).toNat, at_ + 3)
    else if l0 == 0x82 then ((b.get! (at_ + 2)).toNat * 256 + (b.get! (at_ + 3)).toNat, at_ + 4)
    else (0, 0)
  if start == 0 || start + len > b.size then
    throw <| IO.userError s!"{where_}: bad DER length at {at_}"
  pure (b.get! at_, start, start + len)

/-- The key type and key data of the `SignedKey` in an extension value,
and its signature (tls.md: `SignedKey ::= SEQUENCE { publicKey OCTET
STRING, signature OCTET STRING }`; the public key is the protobuf
`PublicKey { Type = 1; Data = 2 }`). -/
private def signedKey (where_ : String) (ext : ByteArray) : IO (Nat × ByteArray × ByteArray) := do
  let (t0, s0, _) ← tlv where_ ext 0
  let (t1, s1, e1) ← tlv where_ ext s0
  let (t2, s2, e2) ← tlv where_ ext e1
  unless t0 == 0x30 && t1 == 0x04 && t2 == 0x04 do
    throw <| IO.userError s!"{where_}: not a SignedKey"
  let pk := ext.extract s1 e1
  -- The protobuf: 0x08 <type>, then 0x12 <varint length> <data>.
  unless pk.get! 0 == 0x08 && pk.get! 2 == 0x12 do
    throw <| IO.userError s!"{where_}: not a PublicKey protobuf"
  let l0 := (pk.get! 3).toNat
  let (len, start) := if l0 < 0x80 then (l0, 4) else ((l0 - 0x80) + (pk.get! 4).toNat * 128, 5)
  pure ((pk.get! 1).toNat, pk.extract start (start + len), ext.extract s2 e2)

/-- The host-key signature check of the TLS handshake, composed from the
backend verifiers: the key type picks the verifier (1 Ed25519, 2
secp256k1, 3 ECDSA), and the message is the prefix and the SPKI. -/
private def hostKeySignatureVerifies (where_ : String) (c : Certificate) : IO Bool := do
  let (kind, key, sig) ← signedKey where_ c.extension
  let msg := ofString "libp2p-tls-handshake:" ++ c.spki
  pure <| match kind with
    | 1 => ed25519Verify key msg sig
    | 2 => secp256k1Verify key msg sig
    | 3 => p256Verify key msg sig
    | _ => false

/-- 2026-01-01T00:00:00Z: a fixed "now" for the validity comparisons. -/
private def fixedNow : Int := 1767225600

private def specCertificates (r : Runner) : IO Unit := do
  let file := "tls-ext.json"
  let j ← loadJson file
  let oid := "1.3.6.1.4.1.53594.1.1"
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    let der ← unhexX file (← jStr file c "certHex")
    r.check s!"TLS spec certificate {name}: the self-signature verifies" (selfSigned der)
    match inspect der oid with
    | .error e => r.check s!"TLS spec certificate {name}: inspect failed with {repr e}" false
    | .ok cert =>
      r.check s!"TLS spec certificate {name}: NotBefore is 1975-01-01 13:00:00 UTC"
        (cert.notBefore == 157813200)
      r.check s!"TLS spec certificate {name}: NotAfter is 4096-01-01 13:00:00 UTC"
        (cert.notAfter == 67090165200)
      r.check s!"TLS spec certificate {name}: valid at the fixed time" (cert.validAt fixedNow)
      let ok ← hostKeySignatureVerifies file cert
      if name == "invalid" then
        r.check "TLS spec certificate invalid: the host-key signature fails" (!ok)
      else
        r.check s!"TLS spec certificate {name}: the host-key signature verifies" ok
  -- A truncated certificate does not parse.
  let some first := (← jArr file j "cases").head? | throw <| IO.userError s!"{file}: no cases"
  let der ← unhexX file (← jStr file first "certHex")
  r.check "a truncated certificate is invalidCertificate"
    (failsWith .invalidCertificate (inspect (der.extract 0 (der.size - 1)) oid))
  r.check "a truncated certificate fails the self-signature check"
    (!selfSigned (der.extract 0 (der.size - 1)))
  r.check "a certificate with a trailing byte is invalidCertificate"
    (failsWith .invalidCertificate (inspect (der.push 0) oid))

private def fixtureCertificates (r : Runner) : IO Unit := do
  let file := "backend-strictness.json"
  let j ← loadFixture file
  let oid ← jStr file j "requiredOid"
  let value ← unhexX file (← jStr file j "extensionValueHex")
  for c in ← jArr file j "certificates" do
    let name ← jStr file c "name"
    let der ← unhexX file (← jStr file c "certHex")
    let nb : Int := ← jNat file c "notBefore"
    let na : Int := ← jNat file c "notAfter"
    let why ← jStr file c "why"
    match ← jStr file c "expect", inspect der oid with
    | "reject", res =>
      r.check s!"X.509 fixture {name}: invalidCertificate ({why})"
        (failsWith .invalidCertificate res)
    | "accept", .ok cert =>
      r.check s!"X.509 fixture {name}: accepted, value and times match ({why})"
        (cert.extension == value && cert.notBefore == nb && cert.notAfter == na &&
          cert.validAt fixedNow && selfSigned der)
    | "expired", .ok cert =>
      r.check s!"X.509 fixture {name}: parses with its times" (cert.notBefore == nb && cert.notAfter == na)
      r.check s!"X.509 fixture {name}: not valid at the fixed time ({why})" (!cert.validAt fixedNow)
      r.check s!"X.509 fixture {name}: valid at both ends of its period, not one second after"
        (cert.validAt nb && cert.validAt na && !cert.validAt (na + 1) && !cert.validAt (nb - 1))
    | "badSelfSignature", .ok _ =>
      r.check s!"X.509 fixture {name}: parses, and the self-signature check fails ({why})"
        (!selfSigned der)
    | expect, .error e =>
      r.check s!"X.509 fixture {name}: expected {expect}, inspect failed with {repr e}" false
    | expect, .ok _ => r.check s!"X.509 fixture {name}: expected {expect}, inspect accepted" false

def BackendX509.run (r : Runner) : IO Unit := do
  r.section "crypto/backend X.509" "libp2p/specs tls/tls.md; generated fixtures"
  specCertificates r
  fixtureCertificates r

end Tests
