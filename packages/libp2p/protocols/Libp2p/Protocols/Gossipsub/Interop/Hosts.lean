import Lean
import Multiformats.Multiaddr.Ip

/-!
# Shadow hosts resolution

Shadow writes one hosts file per simulated node. Each file keeps the
loopback row and adds one IPv4 row per simulated host, for example
`11.0.0.1 node0`. The probe in GATE-PROBES-2026-11-06.md confirmed the
format, so the adapter resolves `nodeN` from that file instead of calling
`getaddrinfo` through FFI.

This module keeps the parsing pure. `parseHosts` and `lookup?` run on a
string, so the suite pins them without a filesystem. Only `lookupHostsFile`
reads `/etc/hosts`; it delegates every decision to the pure parser.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Interop

open Multiformats.Multiaddr

/-- A parsed IPv4 address holds its four octets, the wire shape `parseIp4?` returns. -/
abbrev IPv4 := List Nat

/-- Drop the ASCII whitespace a hosts line can carry at either end. -/
private def trim (text : String) : String := text.trimAscii.toString

/-- Reuse the strict dotted-quad parser from the multiformats package. -/
private def parseIPv4? (text : String) : Option IPv4 :=
  match parseIp4? text with
  | .ok bytes => some bytes
  | .error _ => none

/-- Parse one hosts line into an IPv4 address and its exact names.

A line is `<ip> <name> [<alias>...]`. A `#` starts a comment that runs to
the end of the line, spaces and tabs separate fields, and blank fields are
dropped. The line is ignored when the address is not a strict IPv4 value,
when it carries no name, or when it is empty after the comment. IPv6 rows
fail the IPv4 parser and are therefore ignored rather than rejected. -/
private def parseLine (line : String) : Option (IPv4 × List String) :=
  let body := (trim line).splitOn "#" |>.headD "" |>.trimAscii.toString
  let fields := (body.split (fun c => c == ' ' || c == '\t')).toList
  let fields := fields.filter (fun field => !field.isEmpty)
  match fields with
  | address :: names =>
      let address := address.toString
      let names := names.map String.Slice.toString
      if names.isEmpty then none
      else parseIPv4? address |>.map (fun ip => (ip, names))
  | [] => none

/-- Parse hosts content into IPv4 rows with their exact names.

The parser splits on line feeds only. A carriage return survives a split and
the field trim removes it, so CRLF content parses without a second pass. -/
def parseHosts (content : String) : List (IPv4 × List String) :=
  content.splitOn "\n" |>.filterMap parseLine

/-- Find the IPv4 address of one name across primary names and aliases.

The comparison is exact. `node1` does not match the row `11.0.0.3 node10`,
and `node1x` matches nothing, because list equality does not accept a
prefix. The first row that carries the name wins, matching the order the
hosts file states. -/
def lookup? (hosts : List (IPv4 × List String)) (name : String) : Option IPv4 :=
  hosts.find? (fun entry => entry.2.any (fun candidate => candidate == name))
    |>.map Prod.fst

/-- Build the transport address prefix for one resolved address.

The interop transport fixes the port at 9000 (specification section 8).
The caller appends `/p2p/<peer id>` once the identity package derives it,
so this function returns only the prefix it can build from the address. -/
def multiaddrPrefix (ip : IPv4) : Option String :=
  ip4String? ip |>.toOption
    |>.map (fun text => s!"/ip4/{text}/tcp/9000")

/-- Read Shadow's hosts file and resolve one name through the pure parser.

This is the only definition in the module that touches the filesystem, and
it performs no parsing of its own. -/
def lookupHostsFile (name : String) : IO (Option IPv4) := do
  let content ← IO.FS.readFile "/etc/hosts"
  pure (lookup? (parseHosts content) name)

end Libp2p.Protocols.Gossipsub.Interop
