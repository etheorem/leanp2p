import Libp2p.Core.Policy

/-!
# The policy values

The three policy hooks of `libp2p/core` are seams (ARCHITECTURE §3.1):
the connection gater, the resource manager, and the address ranker.
The host takes one value of each in its configuration, and `cli/` or a
consumer may pass its own (the package ARCHITECTURE, "Decisions"). This
module holds the defaults the configuration starts from, and the
denying gater the suites use (the core pair assigned the doubles
here). The limiting values of §9, delta 4, land later behind the same
seams.
-/

set_option autoImplicit false

namespace Libp2p.Host.Policy

open Libp2p.Core

/-- The default gater: it allows every dial, every inbound connection,
and every proved peer. -/
def permissiveGater : ConnectionGater where
  allowDial _ _ := pure true
  allowInbound _ _ := pure true
  allowSecured _ _ _ _ := pure true

/-- The test double that refuses at every checkpoint. A dial fails with
`Host.Error.gated .dial`, and an accepted connection closes before any
byte moves. -/
def denyingGater : ConnectionGater where
  allowDial _ _ := pure false
  allowInbound _ _ := pure false
  allowSecured _ _ _ _ := pure false

/-- A share of no limit: its release returns nothing. -/
private def freeShare : Reservation := { release := pure () }

/-- The default resource manager: it admits every connection, peer,
stream, and buffer, and counts nothing. -/
def unlimited : ResourceManager where
  openConnection _ _ _ := pure (some {
    setPeer := fun _ => pure true
    reserveStream := pure (some freeShare)
    reserveMemory := fun _ => pure (some freeShare)
    release := pure () })

/-- The default address ranker: the addresses in the order given, with
no delay, the form of js-libp2p's `AddressSorter` (the core pair,
`AddressRanker`). -/
def keepOrder : AddressRanker where
  rank addrs := addrs.map fun addr => { addr, delayMs := 0 }

end Libp2p.Host.Policy
