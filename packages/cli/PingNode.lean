import Cli
import Multiformats
import Libp2p.Host.Swarm

/-!
# PingNode

The `pingnode` executable. `Cmd.parse` accepts `serve <port>` or
`dial <multiaddr>`. `Cmd.init` keeps the help and version flags out
of the command. A usage error exits 2, before any host exists.
`splitPeer` drops the trailing peer. A `p2p` component left in the
transport prefix is a usage error. A line break in an operand is
escaped in the usage line. A valid argument list reaches the
unfinished node and exits 1.
-/

set_option autoImplicit false

namespace Cli.PingNode

open Cli
open Libp2p.Host (Host)

/-- One string operand. -/
private def operand (name description : String) : Arg :=
  { name, description, type := String }

/-- A subcommand with one operand and no flags. -/
private def leaf (name argName description : String) : Cmd :=
  .init {
    name
    parentNames := #["pingnode"]
    version? := none
    description
    flags := #[]
    positionalArgs := #[operand argName description]
    variableArg? := none
  } (fun _ => pure 0) #[] none

/-- `serve` and `dial`, and no flags on the root. -/
private def command : Cmd :=
  .init {
    name := "pingnode"
    parentNames := #[]
    version? := none
    description := "Serve or dial a ping."
    flags := #[]
    positionalArgs := #[]
    variableArg? := none
  } (fun _ => pure 0) #[
    leaf "serve" "port" "Listen on a port.",
    leaf "dial" "multiaddr" "Dial a multiaddr."
  ] none

/-- Replace a newline with `\n` and a carriage return with `\r`. -/
private def oneLine (text : String) : String :=
  (text.replace "\r" "\\r").replace "\n" "\\n"

/-- Print one usage line and exit 2. -/
private def usage (line : String) : IO UInt32 := do
  IO.eprintln (oneLine line)
  return 2

/-- The node is not built in this slice. -/
private def unfinished : IO UInt32 := do
  IO.eprintln "pingnode: not implemented"
  return 1

/-- `0`, or a decimal from 1 to 65535 with no leading zero. -/
private def validPort (text : String) : Bool :=
  if text == "0" then true
  else
    text.all Char.isDigit && text.front?.any (· != '0') &&
      match text.toNat? with
      | some n => n ≤ 65535
      | none => false

/-- The operand of the selected subcommand. -/
private def operandValue (parsed : Parsed) (name : String) : Option String :=
  parsed.positionalArg? name |>.map (·.value)

/-- True when `transport` still contains a `/p2p` component. -/
private def transportHasPeer (transport : Multiformats.Multiaddr) : Bool :=
  transport.components.any fun c =>
    decide (c.proto = Multiformats.Protocol.«p2p»)

/-- Accept a final `/p2p/<id>` whose transport prefix has no `/p2p`. -/
private def validDial (text : String) : Except String Unit := do
  let addr ← match Multiformats.Multiaddr.parse? text with
    | .ok addr => pure addr
    | .error err => throw s!"{reprStr err} {text}"
  match Host.splitPeer addr with
  | .ok (transport, some _) =>
    if transportHasPeer transport then
      throw s!"dial address has an earlier /p2p peer: {text}"
    else pure ()
  | .ok (_, none) => throw s!"dial address has no final /p2p peer: {text}"
  | .error err => throw s!"{err} {text}"

/-- Check `args`, then report that the node is not implemented. -/
def main (args : List String) : IO UInt32 := do
  match command.parse args with
  | .error err => usage err.kind.msg
  | .ok (cmd, parsed) =>
    match cmd.meta.name with
    | "serve" =>
      match operandValue parsed "port" with
      | some port =>
        if validPort port then unfinished else usage s!"invalid port: {port}"
      | none => usage "missing port"
    | "dial" =>
      match operandValue parsed "multiaddr" with
      | some text =>
        match validDial text with
        | .ok () => unfinished
        | .error line => usage line
      | none => usage "missing multiaddr"
    | _ => usage "missing subcommand"

end Cli.PingNode

def main : List String → IO UInt32 := Cli.PingNode.main
