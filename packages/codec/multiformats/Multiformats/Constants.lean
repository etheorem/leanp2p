import Std

/-!
# Decode budgets

Each variable-length decoder checks these limits before extracting a
payload. The framing layer can impose a smaller limit on a whole message.
-/

set_option autoImplicit false

namespace Multiformats

/-- Digests are opaque data; this bound also covers variable-length identity hashes. -/
def maxDigestBytes : Nat := 65536

/-- A path or other variable-size component has a separate local budget. -/
def maxComponentBytes : Nat := 65536

/-- The complete address bounds the number of components and every parser traversal. -/
def maxAddressBytes : Nat := 1048576

/-- A JSON string may escape each input byte as six characters, plus two quotes. -/
def maxAddressJsonBytes : Nat := 6 * maxAddressBytes + 2

end Multiformats
