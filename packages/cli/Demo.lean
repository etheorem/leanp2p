/-!
# Demo

The `demo` executable. The entry reports that the node is not
implemented yet, and it exits 1. The W5.8 behavior section is the
contract for the later slices.
-/

set_option autoImplicit false

namespace Cli.Demo

/-- Print the scaffold diagnostic and exit 1. -/
def main (_args : List String) : IO UInt32 := do
  IO.eprintln "demo: not implemented"
  return 1

end Cli.Demo

def main : List String → IO UInt32 := Cli.Demo.main
