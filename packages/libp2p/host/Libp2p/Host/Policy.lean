import Libp2p.Core

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

/-- The admission of an inbound connection, before any byte of its
handshake moves: the gater's `allowInbound` at its two addresses, then
the resource manager's scope (`Core.Admit`). The host runs it on every
accepted TCP connection, and a secured listener runs it on every new
connection. -/
def admission (gater : ConnectionGater) (resources : ResourceManager) : Admit :=
  fun localAddr remoteAddr => do
    if !(← gater.allowInbound localAddr remoteAddr) then return none
    resources.openConnection .responder none remoteAddr

/-- The address ranker that keeps the order given, with no delay, the
form of js-libp2p's `AddressSorter` (the core pair, `AddressRanker`). -/
def keepOrder : AddressRanker where
  rank addrs := addrs.map fun addr => { addr, delayMs := 0 }

/-- True when the address names a QUIC transport: a `quic-v1`
component. -/
def isQuic (a : Multiformats.Multiaddr) : Bool :=
  a.components.any (·.proto == .«quic-v1»)

/-- The default address ranker: the QUIC addresses first, then the
others, each group in the order given, with no delay. The consensus
networking spec: "QUIC is the primary transport. When a peer is
reachable over both TCP and QUIC, clients SHOULD prioritise peer's QUIC
addresses" (`vendor/consensus-specs/specs/phase0/p2p-interface.md`,
lines 160 and 161). -/
def quicFirst : AddressRanker where
  rank addrs :=
    (addrs.filter isQuic ++ addrs.filter (!isQuic ·)).map fun addr => { addr, delayMs := 0 }

/-- The ranker's order: the QUIC addresses in the order given, then the
others in the order given. -/
theorem quicFirst_order (addrs : List Multiformats.Multiaddr) :
    (quicFirst.rank addrs).map (·.addr) = addrs.filter isQuic ++ addrs.filter (!isQuic ·) := by
  -- Reading `addr` back from `{ addr, delayMs := 0 }` is the identity.
  simp [quicFirst, List.map_map, Function.comp_def]

/-- The ranker drops no address and adds none: its addresses are a
permutation of those given. -/
theorem quicFirst_perm (addrs : List Multiformats.Multiaddr) :
    ((quicFirst.rank addrs).map (·.addr)).Perm addrs := by
  rw [quicFirst_order]
  exact List.filter_append_perm isQuic addrs

/-- The ranker sets no dial delay. -/
theorem quicFirst_noDelay (addrs : List Multiformats.Multiaddr) :
    ∀ d ∈ quicFirst.rank addrs, d.delayMs = 0 := by
  intro d h
  simp only [quicFirst, List.mem_map, List.mem_append, List.mem_filter] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

end Libp2p.Host.Policy