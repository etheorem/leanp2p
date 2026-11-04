import Multiformats.Multiaddr.Core
import Multiformats.SequenceOps

/-!
# Checked address operations

Appending may exceed the budget or put a component after a Unix path.
Truncation or splitting can separate an IPv6 zone from its address.
Every operation that constructs an address therefore returns its check
result explicitly. Views and collection operations preserve existing
validated values without another boundary check.
-/

set_option autoImplicit false

namespace Multiformats.Multiaddr

/-- Composition preserves both inputs' components and checks the resulting address. -/
def encapsulate (address extra : Multiaddr) : Except Error Multiaddr :=
  ofFrames? (address.frames ++ extra.frames)

/-- Go's absent-subaddress result is the original address; its empty result is none. -/
def decapsulate? (address sub : Multiaddr) : Except Error (Option Multiaddr) := do
  match SequenceOps.decapsulate? address.frames sub.frames with
  | none => .ok none
  | some kept => some <$> ofFrames? kept

/-- The documented operation name uses the same checked result. -/
def decapsulate (address sub : Multiaddr) : Except Error (Option Multiaddr) :=
  decapsulate? address sub

/-- The JavaScript convention returns a miss for an absent subaddress too. -/
def decapsulateThrow? (address sub : Multiaddr) : Except Error (Option Multiaddr) := do
  match SequenceOps.decapsulateThrow? address.frames sub.frames with
  | none => .ok none
  | some kept => some <$> ofFrames? kept

/-- Truncating before the last protocol still validates the retained prefix. -/
def decapsulateCode (address : Multiaddr) (code : Nat) : Except Error Multiaddr :=
  ofFrames? (SequenceOps.decapsulateCode address.frames code)

/-- A split that isolates an IPv6 zone reports an invalid standalone address. -/
def split (address : Multiaddr) : Except Error (List Multiaddr) :=
  address.frames.mapM (fun frame => ofFrames? [frame])

/-- Joined sequences must still satisfy the whole-address budget and ordering. -/
def join (addresses : List Multiaddr) : Except Error Multiaddr :=
  ofFrames? (addresses.flatMap frames)

/-- The protocol view preserves every occurrence and its wire order. -/
def protocols (address : Multiaddr) : List (Nat × String) := SequenceOps.protocols address.frames

/-- The component text view follows the decoded-path convention of the JS suite. -/
def getComponents (address : Multiaddr) : List SequenceOps.ComponentView :=
  SequenceOps.components address.frames

/-- The first occurrence wins; a valueless protocol returns an empty string. -/
def valueForProtocol? (address : Multiaddr) (code : Nat) : Option String :=
  SequenceOps.valueForProtocol? address.frames code

/-- The operation without the optional suffix retains the same lookup semantics. -/
def valueForProtocol (address : Multiaddr) (code : Nat) : Option String :=
  valueForProtocol? address code

/-- Name-only parsing is separate from complete address parsing. -/
def protocolsWithString? (text : String) : Option (List (Nat × String)) :=
  SequenceOps.protocolsWithString? text

/-- Equality compares the complete canonical wire value. -/
def equal (left right : Multiaddr) : Bool := left == right

/-- Membership uses the same canonical identity as the codec. -/
def contains (addresses : List Multiaddr) (address : Multiaddr) : Bool := addresses.contains address

/-- Keep the first occurrence and preserve the caller's order. -/
def unique (addresses : List Multiaddr) : List Multiaddr :=
  (addresses.foldl (fun reversed address =>
    if reversed.contains address then reversed else address :: reversed) []).reverse

/-- The upstream-style spelling remains available to callers. -/
def uniqueAddrs (addresses : List Multiaddr) : List Multiaddr := unique addresses

/-- Filtering preserves the relative order of all retained addresses. -/
def filter (addresses : List Multiaddr) (predicate : Multiaddr → Bool) : List Multiaddr :=
  addresses.filter predicate

/-- The upstream-style spelling shares the same collection operation. -/
def filterAddrs (addresses : List Multiaddr) (predicate : Multiaddr → Bool) : List Multiaddr :=
  filter addresses predicate

end Multiformats.Multiaddr
