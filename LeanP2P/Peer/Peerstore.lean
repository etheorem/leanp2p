import LeanP2P.Crypto.PeerId
import LeanP2P.Net.Multiaddr
/-!
# Peerstore

Address/key cache keyed by PeerId. Assoc lists are fine at spike scale.
-/

namespace LeanP2P

structure Peerstore where
  addrs : IO.Ref (List (PeerId × List Multiaddr))
  keys : IO.Ref (List (PeerId × PubKey))

def Peerstore.new : IO Peerstore := do
  return { addrs := ← IO.mkRef [], keys := ← IO.mkRef [] }

def Peerstore.addAddrs (ps : Peerstore) (id : PeerId) (as : List Multiaddr) : IO Unit := do
  let cur ← ps.addrs.get
  match cur.lookup id with
  | some old => ps.addrs.set (cur.replace (id, old) (id, old ++ as))
  | none => ps.addrs.set ((id, as) :: cur)

def Peerstore.addrsOf (ps : Peerstore) (id : PeerId) : IO (List Multiaddr) := do
  return (← ps.addrs.get).lookup id |>.getD []

def Peerstore.addKey (ps : Peerstore) (id : PeerId) (k : PubKey) : IO Unit := do
  let cur ← ps.keys.get
  unless cur.any (·.1 == id) do
    ps.keys.set ((id, k) :: cur)

def Peerstore.keyOf (ps : Peerstore) (id : PeerId) : IO (Option PubKey) := do
  return (← ps.keys.get).lookup id

end LeanP2P
