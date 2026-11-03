import Backend
import LeanHazmatP256

/-!
# The route for ECDSA P-256 verification

Root ARCHITECTURE §4.6 routes ECDSA P-256 verification to the etheorem
package `LeanHazmatP256`. That package verifies through a raw
interface: five 32-byte big-endian fields, the message hash, `r`, `s`,
and the affine point `(qx, qy)`. The callers of the facade hold a key
as SubjectPublicKeyInfo DER and a signature as the DER
`ECDSA-Sig-Value`. The backend verifier takes the same two forms. This
module turns the two DER forms into the raw fields and hashes the
message.

**The SPKI form.** An uncompressed P-256 point has one SPKI encoding of
91 bytes (RFC 5480 §2). A fixed 27-byte head names `id-ecPublicKey`
and the `prime256v1` curve, and it opens the BIT STRING with the
`0x04` point tag. `qx` and `qy` follow. The route accepts that encoding
only. Go's `crypto/x509` parses the point with
`ecdsa.ParseUncompressedPublicKey`, so Go rejects a compressed point
too (facade ARCHITECTURE, contract 2).

**The signature form.** `ECDSA-Sig-Value` is a SEQUENCE of two
INTEGERs (RFC 3279 §2.2.3). Strict DER (X.690 §10) fixes one encoding
per value: the short length form below 128, the minimal INTEGER, and
no trailing byte. A P-256 signature body is at most 70 bytes, so the
short form always applies. OpenSSL 3 rejects a non-canonical signature
as well, so the backend verifier and this route agree on that input.

**The fold.** `verify` returns `Bool`. `false` covers every input that
does not parse, a SHA-256 fault, and a signature that does not verify.
The etheorem verifier states the same fold.

**High S.** §4.6 gives P-256 no low-S rule. The etheorem verifier
accepts a high S, and so does OpenSSL. The suite pins that both sides
accept the high-S twin.
-/

set_option autoImplicit false

namespace Crypto.P256

/-- The size of one raw field: a P-256 coordinate or scalar. The layout
facts live in `Backend.Sign`, the one home both verifiers read. -/
abbrev fieldSize : Nat := Backend.p256FieldSize

/-- The coordinates `(qx, qy)` of an SPKI DER P-256 key, or `none` for
any other byte string. `none` has one meaning: the input is not the
SPKI of an uncompressed P-256 point (`Backend.p256SpkiUncompressed`).
The verifier checks that the point is on the curve. -/
def spkiPoint? (spki : ByteArray) : Option (ByteArray × ByteArray) :=
  let head := Backend.p256SpkiHead.size
  if Backend.p256SpkiUncompressed spki then
    some (spki.extract head (head + fieldSize),
      spki.extract (head + fieldSize) Backend.p256SpkiSize)
  else none

/-- `digits` with zero bytes on the left, up to `fieldSize`. The caller
has checked that `digits` is at most `fieldSize` bytes. -/
private def padField (digits : ByteArray) : ByteArray :=
  ByteArray.mk (Array.replicate (fieldSize - digits.size) 0) ++ digits

/-- The DER INTEGER that starts at `pos`: its value as a raw field, and
the offset after it. `none` for a wrong tag, a length that runs past
the input, a negative value, a non-minimal encoding, or a value longer
than a field. -/
def derUInt? (sig : ByteArray) (pos : Nat) : Option (ByteArray × Nat) := do
  -- `xs[i]?` is the checked read: `none` past the end. The `do` block
  -- of `Option` stops at the first `none`, and `guard` gives `none`
  -- when its condition is false.
  guard (sig[pos]? == some 0x02)
  let len := (← sig[pos + 1]?).toNat
  let stop := pos + 2 + len
  guard (1 ≤ len && stop ≤ sig.size)
  let body := sig.extract (pos + 2) stop
  let first ← body[0]?
  -- X.690 §8.3: the top bit of the first byte is the sign.
  guard (first < 0x80)
  -- X.690 §8.3.2 allows a leading zero byte only to clear the sign
  -- bit of the byte after it.
  let digits ←
    if first == 0 && len > 1 then do
      guard ((← body[1]?) ≥ 0x80)
      pure (body.extract 1 len)
    else pure body
  guard (digits.size ≤ fieldSize)
  pure (padField digits, stop)

/-- The fields `(r, s)` of a strict DER `ECDSA-Sig-Value`, or `none`. -/
def derSignature? (sig : ByteArray) : Option (ByteArray × ByteArray) := do
  guard (sig[0]? == some 0x30)
  let bodyLen := (← sig[1]?).toNat
  -- The short length form, and the SEQUENCE ends where the input ends.
  guard (bodyLen < 0x80 && 2 + bodyLen == sig.size)
  let (r, next) ← derUInt? sig 2
  let (s, stop) ← derUInt? sig next
  guard (stop == sig.size)
  pure (r, s)

/-- Verify a DER ECDSA signature over SHA-256(`msg`) under an SPKI DER
P-256 key, through `LeanHazmatP256`. The type is the type of the
backend verifier, so one facade line swaps the two. `false` covers
every input that does not parse and every fault. -/
def verify (spki msg sig : ByteArray) : Bool :=
  match spkiPoint? spki, derSignature? sig, Backend.sha256 msg with
  | some (qx, qy), some (r, s), .ok hash => LeanHazmat.P256.p256Verify hash r s qx qy
  | _, _, _ => false

-- `#guard` evaluates with the compiled code at build time, so these
-- assertions fail the build when the parser drifts.
#guard Backend.p256SpkiSize == 91
-- r = 1, s = 0x80: the second INTEGER needs its leading zero.
#guard (derSignature? (ByteArray.mk #[0x30, 0x07, 0x02, 0x01, 0x01, 0x02, 0x02, 0x00, 0x80])).isSome
-- A leading zero before a byte below 0x80 is not minimal.
#guard (derSignature? (ByteArray.mk #[0x30, 0x07, 0x02, 0x01, 0x01, 0x02, 0x02, 0x00, 0x7f])).isNone
-- 0x80 alone is negative.
#guard (derSignature? (ByteArray.mk #[0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x80])).isNone
-- One byte after the SEQUENCE.
#guard (derSignature? (ByteArray.mk #[0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x01, 0x00])).isNone

end Crypto.P256
