/-!
# The backend error

`CryptoError` is the one error inductive of `crypto/backend` (root
ARCHITECTURE §3.5). A pure shim binding answers `Option ByteArray`, and
the Lean interface lifts `none` into this type once, in the binding
modules. Each lift picks the arm that names the likely cause, and the
binding's docstring states the choice. `Option` alone cannot say which
input was bad.

One binding answers more than `none`: `Backend.X509.inspect` reports
which rule a refused certificate broke, as a `CertificateRejection`.

Two arms carry a contract of their own. `authFailed` means a failed
ChaCha20-Poly1305 open and nothing else. So the Noise layer maps it to
a protocol error and keeps a library fault apart (§3.5, §4.9). `fault`
means the library failed on inputs the Lean side already checked. No
correct input causes it.
-/

set_option autoImplicit false

namespace Backend

/-- Why `Backend.X509.inspect` refused a certificate: one arm per rule,
so a caller can name the rule that failed. -/
inductive CertificateRejection where
  /-- The DER does not parse as one certificate, has trailing bytes, or
  holds a time or a subject key the shim cannot read. -/
  | malformed
  /-- The required extension is missing. -/
  | missingExtension
  /-- An extension appears twice (RFC 5280 §4.2). -/
  | duplicateExtension
  /-- An extension is critical, and it is neither the required one nor
  one that OpenSSL understands. -/
  | unknownCriticalExtension
  deriving BEq, DecidableEq, Repr

/-- Why a backend call failed. -/
inductive CryptoError where
  /-- The AEAD tag did not verify: the ciphertext, the associated data,
  the key, or the nonce differs from the sealing side. -/
  | authFailed
  /-- The key bytes did not load as the key type the call names. Causes:
  a DER parse failure, the wrong algorithm or curve, an RSA size outside
  2048 to 8192 bits, an X25519 peer key of small order. -/
  | invalidKey
  /-- An argument is out of the range the primitive defines, for example
  an HKDF output longer than 255 hash blocks. -/
  | invalidInput
  /-- An X.509 certificate that does not parse, or that breaks the
  extension rules of `Backend.X509.inspect`; `why` names the rule. -/
  | invalidCertificate (why : CertificateRejection)
  /-- The library failed on inputs the Lean side had checked. -/
  | fault
  deriving BEq, DecidableEq, Repr

/-- The one lift of a shim answer (§3.6): `none` becomes the arm `e`,
and `some b` becomes `b`. The binding modules pick `e` per call. -/
def liftShim {α : Type} (e : CryptoError) : Option α → Except CryptoError α
  | some b => .ok b
  | none => .error e

end Backend
