import Std.Data.HashMap
import Multiformats
import Libp2p.Host.Mock.Identity

/-!
# The peerstore

The third host registry (ARCHITECTURE §3.8): the addresses of each
peer. `dialPeer` walks them. The table changes only through the pure
updates here, applied under `OnceRef.update` (the package
ARCHITECTURE, contract 1). The spike's peerstore lost addresses
through a get-then-set; one atomic update per add closes that race
(PRINCIPLES 3.3).

An add skips the addresses the peer already has, so a redial that
re-adds its address grows nothing. The addresses keep the order they
first arrived in. Limits and TTLs are §9 delta 3, outside this unit
(contract 9).
-/

set_option autoImplicit false

namespace Libp2p.Host

open Multiformats Libp2p.Host.Mock.Identity

/-- The addresses of each peer, in the order they first arrived. A
synonym with no invariant of its own (§3.7). -/
abbrev Peerstore := Std.HashMap PeerId (Array Multiaddr)

namespace Peerstore

/-- Add `addrs` to the addresses of `peer`, and skip each one the peer
already has, so the result holds every address once. -/
def addAddrs (peer : PeerId) (addrs : List Multiaddr) (s : Peerstore) : Peerstore :=
  let known := s.getD peer #[]
  let grown := addrs.foldl (fun acc a => if acc.contains a then acc else acc.push a) known
  s.insert peer grown

/-- The addresses of `peer`, in the order they first arrived. Empty
when the store knows none. -/
def addrsOf (s : Peerstore) (peer : PeerId) : List Multiaddr :=
  (s.getD peer #[]).toList

end Peerstore

end Libp2p.Host
