import LeanP2P.Net.Multiaddr
/-!
# Transport interface

The dial/listen seam. libp2p has interface + registry; here the spike
evaluates plain first-class `structure` values (runtime dispatch, easy to
compose and mock) instead of typeclasses, since implementations are chosen
dynamically at the address/negotiation layer.
-/

namespace LeanP2P

/-- A raw connection: bytes in, bytes out. `read` returning `none` means EOF. -/
structure Connection where
  read : IO (Option ByteArray)
  write : ByteArray → IO Unit
  close : IO Unit
  localAddr : Multiaddr
  remoteAddr : Multiaddr

/-- A listening endpoint. -/
structure Listener where
  addr : Multiaddr
  accept : IO (Option Connection)
  close : IO Unit

/-- A transport can dial addresses and listen on them. -/
structure Transport where
  name : String
  dial : Multiaddr → IO (Option Connection)
  listen : Multiaddr → IO (Option Listener)

def Connection.writeStr (c : Connection) (s : String) : IO Unit :=
  c.write s.toUTF8

/-- Accumulate reads until exactly `n` bytes are available (or EOF). -/
partial def Connection.readExactly (c : Connection) (n : Nat) : IO (Option ByteArray) := do
  let rec loop (acc : ByteArray) : IO (Option ByteArray) := do
    if acc.size ≥ n then
      return some (acc.extract 0 n)
    else
      match ← c.read with
      | none => return none
      | some chunk => loop (acc ++ chunk)
  loop ByteArray.empty

end LeanP2P
