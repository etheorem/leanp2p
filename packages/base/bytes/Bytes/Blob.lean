import Bytes.Text

/-!
# `Blob`: bytes inside core data

A pure core keeps its state, inputs, and outputs as plain data that
derives `Repr` and `DecidableEq`, so a test compares them by value and
prints the difference (ARCHITECTURE §3.3). Core Lean gives `ByteArray`
no `Repr`, and §3.2 forbids an instance on a core type, so a core wraps
its bytes in `Blob`. The yamux, mplex, and Noise cores share this one
wrapper, so the instance has one home (§3.8).
-/

set_option autoImplicit false

namespace Bytes

/-- Bytes inside core data. The `Repr` instance prints hex, which keeps
a key or a frame short in a failed test. -/
structure Blob where
  /-- The bytes. -/
  bytes : ByteArray
  deriving DecidableEq

instance : Repr Blob where
  reprPrec b prec := Repr.addAppParen ("Bytes.Blob.mk 0x" ++ toHex b.bytes) prec

end Bytes
