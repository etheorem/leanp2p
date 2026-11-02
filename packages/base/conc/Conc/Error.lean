/-!
# The error of `conc`

The package owns one error inductive (ARCHITECTURE §3.5). It names the
two failed answers that a `conc` primitive gives its caller.
-/

set_option autoImplicit false

namespace Conc

/-- The answer of a failed `conc` operation. -/
inductive Error where
  /-- The channel closed before it took the value. -/
  | closed
  /-- The deadline expired before the work ended. -/
  | deadlineExpired
  deriving DecidableEq, Repr, Hashable

/-- The two answers differ. `DecidableEq` gives `decide` its instance. -/
example : Error.closed ≠ Error.deadlineExpired := by decide

end Conc
