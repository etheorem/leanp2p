/-!
# The backend error

`CryptoError` is the one error inductive of `crypto/backend` (root
ARCHITECTURE §3.5). A pure shim binding answers `Option ByteArray`, and
the Lean interface lifts `none` into this type once, in the binding
modules. Each lift picks the arm that names the likely cause, and the
binding's docstring states the choice. `Option` alone cannot say which
input was bad.

Two arms carry a contract of their own. `authFailed` is a failed
ChaCha20-Poly1305 open and nothing else, so the Noise layer maps it to a
protocol error and keeps a library fault apart (§3.5, §4.9). `fault`
is the library failing on inputs the Lean side already checked, which
no correct input causes.
-/

set_option autoImplicit false

namespace Backend

/-- Why a backend call failed. -/
inductive CryptoError where
  /-- The AEAD tag did not verify: the ciphertext, the associated data,
  the key, or the nonce differs from the sealing side. -/
  | authFailed
  /-- The key bytes did not load as the key type the call names: a DER
  parse failure, the wrong algorithm or curve, an RSA size outside 2048
  to 8192 bits, or an X25519 peer key of small order. -/
  | invalidKey
  /-- An argument is out of the range the primitive defines, for example
  an HKDF output longer than 255 hash blocks. -/
  | invalidInput
  /-- An X.509 certificate that does not parse, or that breaks the
  extension rules of `Backend.X509.inspect`. -/
  | invalidCertificate
  /-- The library failed on inputs the Lean side had checked. -/
  | fault
  deriving BEq, DecidableEq, Repr

/-- The one lift of a shim answer (§3.6): `none` becomes the arm `e`,
and `some b` becomes `b`. The binding modules pick `e` per call. -/
def liftShim {α : Type} (e : CryptoError) : Option α → Except CryptoError α
  | some b => .ok b
  | none => .error e

end Backend
