import Std.Net.Addr

/-!
# Mock: the multiaddr surface of `codec/multiformats`

W2.3 (`codec/multiformats`) is still open, so this package builds
against a mock of the multiaddr part of its surface (RULES.md, "Working
ahead of the tree"; ARCHITECTURE §4.4). The mock imports nothing from
`Multiformats`. When W2.3 merges, the package drops this module, and
each `open` of `Streams.Mock.Multiformats` becomes an `open` of
`Multiformats`.

## What the mock covers

The mock is narrow. It knows four protocols: `ip4`, `ip6`, `tcp`, and
`memory`. The sim and the TCP stub use these four and no other
(`vendor/multiaddr/protocols.csv` gives the codes and the sizes). The
real package parses the full protocol table, and its text parser is
strict (§4.4). The mock parser accepts the four forms below and
rejects every other text:

* `/ip4/<a.b.c.d>`: a 4-byte value. `Std.Net.IPv4Addr.ofString` parses
  the text.
* `/ip6/<text>`: a 16-byte value. `Std.Net.IPv6Addr.ofString` parses
  the text.
* `/tcp/<port>`: a 2-byte big-endian value below 65536.
* `/memory/<n>`: an 8-byte big-endian value below 2 ^ 64. The real
  package also gives `memory` 8 bytes.

For the text of any other protocol, the mock answers `unknownProtocol`,
and the real package parses it. The suites of this package use the four
forms alone.

## The forms

`Protocol`, `Component`, `Multiaddr`, and `Error` are copies of the
real shapes, reduced to the four protocols and the three errors that
the parser can give. The structure fields keep their real names, so a
pattern match on `components` reads the same after the swap. The
functions are `opaque`, with bodies, as in `Streams.Mock.Bytes`. The
mock states no axiom.
-/

set_option autoImplicit false

namespace Streams.Mock.Multiformats

/-- The four protocols of the mock. -/
inductive Protocol where
  /-- An IPv4 address, 4 bytes. -/
  | «ip4»
  /-- An IPv6 address, 16 bytes. -/
  | «ip6»
  /-- A TCP port, 2 bytes big-endian. -/
  | «tcp»
  /-- An in-memory port, 8 bytes big-endian. -/
  | «memory»
  deriving DecidableEq, Repr

/-- The name of a protocol in the text form. -/
def Protocol.name : Protocol → String
  | .«ip4» => "ip4"
  | .«ip6» => "ip6"
  | .«tcp» => "tcp"
  | .«memory» => "memory"

/-- The value size of a protocol, in bytes. -/
def Protocol.valueBytes : Protocol → Nat
  | .«ip4» => 4
  | .«ip6» => 16
  | .«tcp» => 2
  | .«memory» => 8

/-- One multiaddr component: the protocol and its value bytes, over the
byte model. -/
structure Component where
  /-- The protocol. -/
  proto : Protocol
  /-- The value bytes. -/
  value : List Nat
  deriving DecidableEq, Repr

/-- The check of a component list: at least one component, and every
value holds bytes of its protocol's size. -/
opaque Multiaddr.check (cs : List Component) : Bool :=
  !cs.isEmpty && cs.all fun c => c.value.length == c.proto.valueBytes && c.value.all (· < 256)

/-- A validated multiaddr: the components in wire order, with the proof
that the list passed `Multiaddr.check`. -/
structure Multiaddr where
  /-- The components, in wire order. -/
  components : List Component
  /-- The list passed the check. -/
  valid : Multiaddr.check components = true
  deriving DecidableEq, Repr

/-- A failed multiaddr parse. -/
inductive Error where
  /-- A protocol name outside the four of the mock. -/
  | unknownProtocol
  /-- A value that fails its protocol's check. -/
  | badValue
  /-- A text without the leading `/`, an empty address, or a protocol
  whose value is missing. -/
  | badAddress
  deriving DecidableEq, Repr, BEq

namespace Multiaddr

/-- The address of a component list, when the list passes the check. -/
opaque ofComponents? (cs : List Component) : Option Multiaddr :=
  if h : check cs = true then some ⟨cs, h⟩ else none

/-- The big-endian bytes of `n`, `k` bytes long. -/
private def bigEndian (k n : Nat) : List Nat :=
  (List.range k).reverse.map fun i => n / 256 ^ i % 256

/-- The value of big-endian bytes. -/
private def ofBigEndian (l : List Nat) : Nat :=
  l.foldl (fun acc x => acc * 256 + x) 0

/-- The value bytes of one text value. -/
private def valueOf? (p : Protocol) (text : String) : Option (List Nat) :=
  match p with
  | .«ip4» => (Std.Net.IPv4Addr.ofString text).map fun a => a.octets.toList.map (·.toNat)
  | .«ip6» =>
    (Std.Net.IPv6Addr.ofString text).map fun a =>
      a.segments.toList.flatMap fun s => bigEndian 2 s.toNat
  | .«tcp» => text.toNat?.bind fun n => if n < 65536 then some (bigEndian 2 n) else none
  | .«memory» => text.toNat?.bind fun n => if n < 2 ^ 64 then some (bigEndian 8 n) else none

/-- The protocol of a name. -/
private def protocolOf? : String → Option Protocol
  | "ip4" => some .«ip4»
  | "ip6" => some .«ip6»
  | "tcp" => some .«tcp»
  | "memory" => some .«memory»
  | _ => none

/-- The components of the text segments after the leading `/`: a name,
then its value, for each component. -/
private def componentsOf? : List String → Except Error (List Component)
  | [] => .ok []
  | [name] => if (protocolOf? name).isSome then .error .badAddress else .error .unknownProtocol
  | name :: value :: rest =>
    match protocolOf? name with
    | none => .error .unknownProtocol
    | some p =>
      match valueOf? p value with
      | none => .error .badValue
      | some v => (componentsOf? rest).map (⟨p, v⟩ :: ·)

/-- A multiaddr from its text form, for the four forms of the module
doc. -/
opaque parse? (s : String) : Except Error Multiaddr :=
  match s.splitOn "/" with
  | "" :: segments@(_ :: _) =>
    match componentsOf? segments with
    | .error e => .error e
    | .ok cs => if h : check cs = true then .ok ⟨cs, h⟩ else .error .badAddress
  | _ => .error .badAddress

/-- The text of one component value. -/
private def valueText (c : Component) : String :=
  match c.proto, c.value with
  | .«ip4», [a, b, x, d] =>
    toString (Std.Net.IPv4Addr.ofParts (UInt8.ofNat a) (UInt8.ofNat b) (UInt8.ofNat x)
      (UInt8.ofNat d))
  | .«ip6», v =>
    let seg (i : Nat) : UInt16 := UInt16.ofNat (ofBigEndian ((v.drop (2 * i)).take 2))
    toString (Std.Net.IPv6Addr.ofParts (seg 0) (seg 1) (seg 2) (seg 3) (seg 4) (seg 5) (seg 6)
      (seg 7))
  | _, v => toString (ofBigEndian v)

/-- The address for a message: its text form. -/
opaque describe (m : Multiaddr) : String :=
  String.join (m.components.map fun c => "/" ++ c.proto.name ++ "/" ++ valueText c)

end Multiaddr

end Streams.Mock.Multiformats
