import Std

/-!
# `DecodeError`

The shared error vocabulary of every codec in the tree (ARCHITECTURE
§3.2, §5.2). The two constructors answer different questions, and the
layer above acts on the difference.

- `truncated` reports an input that ended while more bytes could still
  complete the value. The caller keeps waiting.
- `malformed` reports a specification violation. The caller tears the
  connection down.

A model decoder sees a finite list, so it cannot report an end of
stream. ARCHITECTURE §3.5 keeps the end of stream on `Option` and
failure on `Except`.
-/

set_option autoImplicit false

namespace Bytes

/-- Why a decoder refused a byte sequence. -/
inductive DecodeError where
  /-- The input ended, and more bytes could still complete the value. -/
  | truncated
  /-- The input violated the specification. This is a protocol error. -/
  | malformed
  deriving Repr, DecidableEq, BEq, Hashable

end Bytes
