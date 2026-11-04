import CliApp.Demo

/-! # The demo executable -/

set_option autoImplicit false

/-- The program edge runs the demo's async composition. -/
def main (args : List String) : IO UInt32 := CliApp.Demo.runWith {} args
