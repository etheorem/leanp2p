import Backend.Error

/-!
# X.509 helpers

The bindings of `c/p2pcrypto.c` for one self-signed X.509 certificate
(RFC 5280) that carries a key-binding extension. A caller names the
extension by its OID. The helpers know no protocol of their own.

**The rules (root ARCHITECTURE §4.6).** `inspect` rejects a certificate
in four cases, and the error names the case (`CertificateRejection`):
- the DER does not parse as one certificate (`malformed`),
- the named extension is missing (`missingExtension`),
- any extension appears twice, RFC 5280 §4.2 (`duplicateExtension`),
- an extension is critical and unknown (`unknownCriticalExtension`).

A critical extension counts as known when it is the named one or one
that OpenSSL understands (`X509_supported_extension`), such as
`basicConstraints`. The TLS spec asks an endpoint to abort only on the
critical extensions it does not understand. The Go implementation
leaves the known ones to Go's `crypto/x509`. `inspect` ignores a
non-critical extension with another OID.

`selfSigned` checks the certificate's signature under its own subject
key. It accepts SHA-256, SHA-384, SHA-512, and Ed25519 signatures, the
set Go accepts. It accepts an RSA subject key of 2048 to 8192 bits
only.

**Validity is the caller's comparison.** `inspect` returns the
NotBefore and NotAfter times as seconds since the Unix epoch, and it
does not judge them. So the pure binding never reads the clock. The
caller compares the times with `Certificate.validAt` against its
`Clock` seam (§3.1).

**Ownership and trust.** The shim borrows every argument of the
`@[extern]` declarations below (`@&`), as in `Backend.Sym`. `inspect`
and `selfSigned` are pure bindings. One certificate gives the same
answer every time, and the shim reads no global state. `issue` runs in
`IO`, since it draws randomness (§3.6). The library is the toolchain's
bundled OpenSSL 3, which `lean-toolchain` pins. `#print axioms` does
not list an `opaque` constant, so this docstring is the record of the
assumption. `Tests/BackendX509.lean` pins the helpers by the four
certificates of the TLS spec and by generated fixtures whose file
records their provenance. `Tests/BackendSoak.lean` pins their borrowed
arguments.
-/

set_option autoImplicit false

namespace Backend

/-- The shim's answer, as C lays it out: two objects, then two 64-bit
scalars in declaration order. The times cross as the two's-complement
bits of a signed 64-bit count. The layout is the shim's, so the type
stays private. Callers read `Certificate`. -/
private structure CertificateRaw where
  spki : ByteArray
  extension : ByteArray
  notBefore : UInt64
  notAfter : UInt64

/-- What `inspect` reads from a certificate. -/
structure Certificate where
  /-- The subject public key, as SubjectPublicKeyInfo DER. -/
  spki : ByteArray
  /-- The value of the named extension: the contents of its OCTET STRING. -/
  extension : ByteArray
  /-- NotBefore, in seconds since the Unix epoch. -/
  notBefore : Int
  /-- NotAfter, in seconds since the Unix epoch. -/
  notAfter : Int

/-- The signed value of 64 two's-complement bits. -/
private def signed64 (x : UInt64) : Int :=
  if x.toNat < 2 ^ 63 then x.toNat else (x.toNat : Int) - 2 ^ 64

/-- The shim's answer: the certificate, or the code of the refusal.
Codes 0 to 3 are the constructor indices of `CertificateRejection`, and
code 4 is a required OID that does not parse (`c/p2pcrypto.c`,
`required_extension`). -/
@[extern "leanp2p_x509_inspect"]
private opaque inspectRaw (der : @& ByteArray) (oid : @& String) : Except UInt8 CertificateRaw

@[extern "leanp2p_x509_self_signed"]
private opaque selfSignedRaw (der : @& ByteArray) : Bool

/-- The error of a refusal code (`inspectRaw`). A code the shim does
not define reads as `malformed`, fail-closed. -/
private def rejectionOf : UInt8 → CryptoError
  | 1 => .invalidCertificate .missingExtension
  | 2 => .invalidCertificate .duplicateExtension
  | 3 => .invalidCertificate .unknownCriticalExtension
  | 4 => .invalidInput
  | _ => .invalidCertificate .malformed

/-- Read a DER certificate whose required extension has the dotted OID
`requiredOid`. A refused certificate is `invalidCertificate why`, and
`why` names the broken rule (the module doc). A `requiredOid` that is
no dotted OID is `invalidInput`. -/
def inspect (der : ByteArray) (requiredOid : String) : Except CryptoError Certificate :=
  match inspectRaw der requiredOid with
  | .ok c => .ok ⟨c.spki, c.extension, signed64 c.notBefore, signed64 c.notAfter⟩
  | .error code => .error (rejectionOf code)

/-- True when the certificate's signature verifies under its own subject
key, with an accepted signature algorithm and, for an RSA key, 2048 to
8192 bits. `false` covers a parse failure too, fail-closed. -/
def selfSigned (der : ByteArray) : Bool := selfSignedRaw der

/-- True when `now` (seconds since the Unix epoch) lies in the validity
period, both ends included (RFC 5280 §4.1.2.5). -/
def Certificate.validAt (c : Certificate) (now : Int) : Bool :=
  c.notBefore ≤ now && now ≤ c.notAfter

/-! ## Issue

The other half of the helpers: a self-signed certificate that carries
one extension. The key is a P-256 key from `p256Generate`, and the
signature is ECDSA with SHA-256, the shape that the Go reference of the
TLS spec issues (the package ARCHITECTURE, "Public surface", names
the reference).
`inspect` and `selfSigned` accept every certificate that `issue`
gives. -/

/-- The two's-complement bits of a time that fits 64 bits. -/
private def bits64 (t : Int) : UInt64 :=
  if 0 ≤ t then t.toNat.toUInt64 else (2 ^ 64 - (-t).toNat).toUInt64

@[extern "leanp2p_x509_issue"]
private opaque issueRaw (priv : @& ByteArray) (oid : @& String) (value : @& ByteArray)
  (critical : Bool) (notBefore notAfter : UInt64) : IO (Option ByteArray)

/-- Issue a self-signed certificate for the P-256 key `priv` (SEC1 DER).
The certificate carries the extension `oid` (dotted text) with the DER
contents `value`, critical when `critical` holds. The times are
seconds since the Unix epoch. The serial number and the subject are
random. The shim answers `none` for a key that does not parse as
P-256 and for a library fault alike, so the one lift picks
`invalidKey`, the likely cause (`Backend.CryptoError`). IO: the serial
number and the ECDSA nonce draw from the DRBG. -/
def issue (priv : ByteArray) (oid : String) (value : ByteArray) (critical : Bool)
    (notBefore notAfter : Int) : ExceptT CryptoError IO ByteArray := do
  match ← issueRaw priv oid value critical (bits64 notBefore) (bits64 notAfter) with
  | some der => return der
  | none => throw .invalidKey

example : bits64 (-1) = 0xFFFFFFFFFFFFFFFF := by decide
example : bits64 157813200 = 157813200 := by decide

example : signed64 0xFFFFFFFFFFFFFFFF = -1 := by decide
example : signed64 157813200 = 157813200 := by decide

end Backend
