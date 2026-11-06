import Varint
import Libp2p.Identity.Enr
import Libp2p.Identity.Keys
import Libp2p.Identity.PeerId
import Multiformats.Multiaddr

/-!
# From a node record to libp2p: the peer id and the addresses

Root ARCHITECTURE §8, "ENR ↔ multiaddr/peer-id mapping". discv5 finds
records; a libp2p host dials the addresses with the peer id the record
names.

**The peer id.** The `secp256k1` pair is a compressed SEC1 point, the
`Data` form of a libp2p secp256k1 public key (peer-ids spec). The peer
id derives from that key the way it derives from any libp2p key.

**The addresses.** EIP-778 holds an IPv4 address (`ip`), an IPv6
address (`ip6`), and the ports `tcp`, `udp`, `tcp6`, and `udp6`. "If no
`tcp6` / `udp6` port is provided, the `tcp` / `udp` port applies to
both IP addresses." One multiaddr goes out per address and transport:

| record | multiaddr |
|---|---|
| `ip`, `tcp` | `/ip4/<ip>/tcp/<tcp>` |
| `ip`, `udp` | `/ip4/<ip>/udp/<udp>` |
| `ip6`, `tcp6` or else `tcp` | `/ip6/<ip6>/tcp/<port>` |
| `ip6`, `udp6` or else `udp` | `/ip6/<ip6>/udp/<port>` |

The reverse map reads the IPv4 addresses first. An IPv6 port becomes
`tcp6` or `udp6` only when it differs from the general port, and it
becomes the general port when the record has none. A record in that
form maps out and back to the same pairs.

The binary multiaddr is a varint protocol code, then the value. The
four protocols here carry fixed-size values: 4 and 16 address bytes,
and a 2-byte big-endian port.
-/

set_option autoImplicit false

namespace Libp2p.Identity.Enr

open Bytes Rlp Multiformats

/-! ## The peer id -/

/-- The libp2p peer id of the key that signed the record. -/
def peerId (r : Enr) : Except Error PeerId := do
  let key ← (PubKey.ofData? .secp256k1 (ofNatList r.publicKey)).mapError fun _ => .publicKey
  (PeerId.ofPublicKey key).mapError fun _ => .publicKey

/-! ## The addresses -/

/-- A port as the 2-byte value of a `tcp` or `udp` component. -/
def portValue (port : Nat) : List Nat := [port / 256 % 256, port % 256]

/-- One binary component: the varint code, then the value. -/
def component (proto : Protocol) (value : List Nat) : List Nat :=
  Varint.encodeNat proto.toCode ++ value

/-- The multiaddr of one address and one port. -/
def address (ipProto : Protocol) (ip : List Nat) (transport : Protocol) (port : Nat) :
    Except Error Multiaddr :=
  (Multiaddr.ofByteArray? (ofNatList (component ipProto ip ++
    component transport (portValue port)))).mapError fun _ => .multiaddr

/-- The multiaddrs of a record, in the order of the table above. -/
def multiaddrs (r : Enr) : Except Error (List Multiaddr) := do
  let ip ← r.ip?
  let ip6 ← r.ip6?
  let tcp ← r.port? .tcp
  let udp ← r.port? .udp
  let tcp6 ← r.port? .tcp6
  let udp6 ← r.port? .udp6
  let plan : List (Protocol × List Nat × Protocol × Nat) :=
    (match ip with
      | some a => (tcp.map (.ip4, a, .tcp, ·)).toList ++ (udp.map (.ip4, a, .udp, ·)).toList
      | none => []) ++
    (match ip6 with
      | some a => ((tcp6 <|> tcp).map (.ip6, a, .tcp, ·)).toList ++
          ((udp6 <|> udp).map (.ip6, a, .udp, ·)).toList
      | none => [])
  plan.mapM fun (ipProto, a, transport, port) => address ipProto a transport port

/-! ## The reverse map -/

/-- The parts of one multiaddr: the address protocol and bytes, the
transport, and the port. `none` for any other shape. -/
def parts? (m : Multiaddr) : Option (Protocol × List Nat × Protocol × Nat) := do
  let bytes := toNatList m.toByteArray
  let (code, rest) ← (Varint.decode? bytes).toOption
  let (ipProto, size) ← if code.val = Protocol.ip4.toCode then some (Protocol.ip4, ip4Size)
    else if code.val = Protocol.ip6.toCode then some (Protocol.ip6, ip6Size) else none
  if rest.length < size then none
  let (code, rest') ← (Varint.decode? (rest.drop size)).toOption
  let transport ← if code.val = Protocol.tcp.toCode then some Protocol.tcp
    else if code.val = Protocol.udp.toCode then some Protocol.udp else none
  match rest' with
  | [hi, lo] => some (ipProto, rest.take size, transport, hi * 256 + lo)
  | _ => none

/-- The address values the reverse map collects, one field per key. -/
structure Endpoints where
  ip : Option (List Nat) := none
  ip6 : Option (List Nat) := none
  tcp : Option Nat := none
  udp : Option Nat := none
  tcp6 : Option Nat := none
  udp6 : Option Nat := none

/-- Take one value of an address key: a second, different value is an
error. -/
def merge {α : Type} [DecidableEq α] (k : Key) (old : Option α) (new : α) :
    Except Error (Option α) :=
  match old with
  | none => .ok (some new)
  | some o => if o = new then .ok (some o) else .error (.value k)

/-- The record pairs that a list of multiaddrs maps back to. -/
def pairsOfMultiaddrs (addrs : List Multiaddr) : Except Error (List Pair) := do
  let parts ← addrs.mapM fun m => match parts? m with
    | some p => .ok p
    | none => .error .multiaddr
  -- The IPv4 addresses first: they fix the general ports.
  let mut e : Endpoints := {}
  for (ipProto, a, transport, port) in parts do
    if ipProto = .ip4 then
      e := { e with ip := ← merge .ip e.ip a }
      if transport = .tcp then e := { e with tcp := ← merge .tcp e.tcp port }
      else e := { e with udp := ← merge .udp e.udp port }
  for (ipProto, a, transport, port) in parts do
    if ipProto = .ip6 then
      e := { e with ip6 := ← merge .ip6 e.ip6 a }
      if transport = .tcp then
        if e.tcp = none then e := { e with tcp := some port }
        else if e.tcp ≠ some port then e := { e with tcp6 := ← merge .tcp6 e.tcp6 port }
      else
        if e.udp = none then e := { e with udp := some port }
        else if e.udp ≠ some port then e := { e with udp6 := ← merge .udp6 e.udp6 port }
  let bytesPair (k : Key) (v : Option (List Nat)) : List Pair :=
    (v.map fun b => ⟨k, .bytes b⟩).toList
  let portPair (k : Key) (v : Option Nat) : List Pair :=
    (v.map fun n => ⟨k, .bytes (ofScalar n)⟩).toList
  let pairs := bytesPair .ip e.ip ++ bytesPair .ip6 e.ip6 ++ portPair .tcp e.tcp ++
    portPair .tcp6 e.tcp6 ++ portPair .udp e.udp ++ portPair .udp6 e.udp6
  return pairs.mergeSort fun p q => decide (p.key.name ≤ q.key.name)

/-- The address pairs of a record: the pairs the reverse map rebuilds. -/
def addressPairs (r : Enr) : List Pair :=
  r.pairs.filter fun p => [Key.ip, .ip6, .tcp, .udp, .tcp6, .udp6].contains p.key

end Libp2p.Identity.Enr
