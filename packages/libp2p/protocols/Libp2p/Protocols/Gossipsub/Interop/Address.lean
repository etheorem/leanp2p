import Lean

/-!
# GossipSub interop node addresses

This module implements specification section 7. It accepts only the exact
lowercase prefix node followed by decimal digits. The suffix must be
non-empty, must not have leading zeroes, and must fit an unsigned 64 bit value.
The peer seed writes the node number into the first eight bytes
in little endian order and fills the remaining 24 bytes with zeroes.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Interop

/-- Parse a simulation hostname into its node number. -/
def nodeId? (hostname : String) : Option Nat :=
  if !hostname.startsWith "node" then
    none
  else
    let suffix := (hostname.drop 4).toString
    match suffix.toList with
    | [] => none
    | '0' :: _ :: _ => none
    | chars =>
      if !chars.all (fun c => '0' ≤ c && c ≤ '9') then none
      else match suffix.toNat? with
        | some value => if value ≤ 18446744073709551615 then some value else none
        | none => none

/-- Return one little endian byte from a natural number. -/
def littleEndianByte (value index : Nat) : Nat :=
  (value / (2 ^ (8 * index))) % 256

/-- Build the 32 byte seed used by the interop peer id. -/
def peerSeed (nodeId : Nat) : List Nat :=
  (List.range 8).map (littleEndianByte nodeId) ++ List.replicate 24 0

end Libp2p.Protocols.Gossipsub.Interop
