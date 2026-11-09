import Interop

/-!
# The `interop` executable

The entry point of the transport-interop harness. `Interop.main` holds
the run; this module gives it the top-level name that Lake's executable
expects, and the `Tests` suite imports `Interop` without it.
-/

/-- The `interop` executable. -/
def main : IO UInt32 := Interop.main
