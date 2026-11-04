import CliApp.PingNode

/-! # The ping node executable -/

set_option autoImplicit false

/-- The program edge runs one server or dialer mode. -/
def main (args : List String) : IO UInt32 := CliApp.PingNode.runWith {} args
