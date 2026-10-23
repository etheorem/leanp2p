import LeanP2P.Crypto.PeerId
import LeanP2P.Net.Multiaddr
import LeanP2P.Conc
/-!
# Peerstore

Address/key cache keyed by PeerId. Assoc lists are fine at spike scale;
the cells are mutex-guarded (`OnceRef`) so the read-modify-write in
`addAddrs` cannot lose a concurrent update (dials run on their own
tasks), and re-adding an address (every dial does) must not grow the
list without bound.
-/

namespace LeanP2P

structure Peerstore where
  addrs : OnceRef (List (PeerId × List Multiaddr))
  keys : OnceRef (List (PeerId × PubKey))

def Peerstore.new : IO Peerstore := do
  return { addrs := ← OnceRef.new [], keys := ← OnceRef.new [] }

/-- Add addresses for `id`, deduplicated (a redial re-adds the same
address; the cache must not grow with it). One atomic update. -/
def Peerstore.addAddrs (ps : Peerstore) (id : PeerId) (as : List Multiaddr) : IO Unit := do
  ps.addrs.update fun cur =>
    match cur.lookup id with
    | some old => (cur.replace (id, old) (id, Multiaddr.uniqueAddrs (old ++ as)), ())
    | none => ((id, Multiaddr.uniqueAddrs as) :: cur, ())

def Peerstore.addrsOf (ps : Peerstore) (id : PeerId) : IO (List Multiaddr) := do
  return (← ps.addrs.get).lookup id |>.getD []

def Peerstore.addKey (ps : Peerstore) (id : PeerId) (k : PubKey) : IO Unit := do
  ps.keys.update fun cur =>
    if cur.any (·.1 == id) then (cur, ()) else ((id, k) :: cur, ())

def Peerstore.keyOf (ps : Peerstore) (id : PeerId) : IO (Option PubKey) := do
  return (← ps.keys.get).lookup id

end LeanP2P
