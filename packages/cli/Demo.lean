import Cli

/-!
# Demo

The `demo` executable. `Cmd.parse` checks the argument list. `Cmd.mk`
would add help and version flags, so this command is built with
`Cmd.init` and an empty flag list. A usage error exits 2. An empty
argument list reaches the unfinished node and exits 1.
-/

set_option autoImplicit false

namespace Cli.Demo

open Cli

/-- The command carries no flags and no operands. -/
private def command : Cmd :=
  .init {
    name := "demo"
    parentNames := #[]
    version? := none
    description := "Run the loopback demo."
    flags := #[]
    positionalArgs := #[]
    variableArg? := none
  } (fun _ => pure 0) #[] none

/-- Print one usage line and exit 2. -/
private def usage (line : String) : IO UInt32 := do
  IO.eprintln line
  return 2

/-- The node is not built in this slice. -/
private def unfinished : IO UInt32 := do
  IO.eprintln "demo: not implemented"
  return 1

/-- Check `args`, then report that the node is not implemented. -/
def main (args : List String) : IO UInt32 := do
  match command.parse args with
  | .error err => usage err.kind.msg
  | .ok _ =>
    -- `parse` treats `--` as the end of flags, so an empty command
    -- can still have seen an argument.
    if args.isEmpty then unfinished else usage s!"unexpected argument: {" ".intercalate args}"

end Cli.Demo

def main : List String → IO UInt32 := Cli.Demo.main
