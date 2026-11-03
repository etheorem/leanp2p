import Backend.Error

/-!
# X.509 helpers

The bindings of `c/p2pcrypto.c` for one self-signed X.509 certificate
(RFC 5280) that carries a key-binding extension. A caller names the
extension by its OID; the helpers know no protocol of their own.

**The rules (root ARCHITECTURE §4.6).** `inspect` rejects a certificate
when the named extension is missing or appears twice, and when any other
extension is marked critical: the caller understands only its own
extension, so every other critical one is unknown to it. A non-critical
extension with another OID is ignored. `selfSigned` checks the
certificate's signature under its own subject key.

**Validity is the caller's comparison.** `inspect` returns the NotBefore
and NotAfter times as seconds since the Unix epoch and does not judge
them, so the pure binding never reads the clock. The caller compares
them with `Certificate.validAt` against its `Clock` seam (§3.1).

**Ownership and trust.** Every argument of the `@[extern]` declarations
below is borrowed (`@&`), as in `Backend.Sym`. The library is the
toolchain's bundled OpenSSL 3; `Tests/Backend.lean` pins the helpers by
the four certificates of the TLS spec and by generated fixtures whose
file records their provenance.
-/

set_option autoImplicit false

namespace Backend

/-- The shim's answer, as C lays it out: two objects, then two 64-bit
scalars in declaration order. The times cross as the two's-complement
bits of a signed 64-bit count. -/
structure CertificateRaw where
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

@[extern "leanp2p_x509_inspect"]
private opaque inspectRaw (der : @& ByteArray) (oid : @& String) : Option CertificateRaw

@[extern "leanp2p_x509_self_signed"]
private opaque selfSignedRaw (der : @& ByteArray) : Bool

/-- Read a DER certificate whose required extension has the dotted OID
`requiredOid`. A certificate that does not parse, has trailing bytes,
lacks the extension, carries it twice, or marks another extension
critical is `invalidCertificate`. -/
def inspect (der : ByteArray) (requiredOid : String) : Except CryptoError Certificate :=
  match inspectRaw der requiredOid with
  | some c => .ok ⟨c.spki, c.extension, signed64 c.notBefore, signed64 c.notAfter⟩
  | none => .error .invalidCertificate

/-- True when the certificate's signature verifies under its own subject
key. `false` covers a parse failure too, fail-closed. -/
def selfSigned (der : ByteArray) : Bool := selfSignedRaw der

/-- True when `now` (seconds since the Unix epoch) lies in the validity
period, both ends included (RFC 5280 §4.1.2.5). -/
def Certificate.validAt (c : Certificate) (now : Int) : Bool :=
  c.notBefore ≤ now && now ≤ c.notAfter

example : signed64 0xFFFFFFFFFFFFFFFF = -1 := by decide
example : signed64 157813200 = 157813200 := by decide

end Backend
