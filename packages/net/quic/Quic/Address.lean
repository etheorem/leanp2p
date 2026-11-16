import Streams
import Multiformats.Multiaddr

/-!
# QUIC addresses

A QUIC multiaddr names an IP address, a UDP port, and the QUIC version
(the QUIC spec, `vendor/specs/quic/README.md`, "Multiaddress"):
`/ip4/127.0.0.1/udp/1234/quic-v1` or `/ip6/…/udp/…/quic-v1`. This package
speaks RFC 9000 only, so the `/quic` component of draft-29, which the
spec phases out, is no address of this package.

The module converts between three forms of one address:

* the multiaddr, the form the host and the peerstore hold;
* the `Std` socket address, the form the UDP socket takes;
* the shim's bytes (`native/c/quic_shim.c`, "Addresses"): the family
  byte 4 or 6, the IP address in network order, then the port,
  big-endian. The layout is a pure codec over the byte model
  (`ShimAddr`), and its round trip is a theorem (`ShimAddr.decode_encode`).

The 16-bit helpers come from `Streams.Tcp`, the one home of the IP and
port byte layout, and their round trips are theorems there.
-/

set_option autoImplicit false

namespace Quic

open Multiformats Streams.Tcp

/-! ## The shim's bytes -/

/-- An address in the shim's layout, over the byte model: the IP
address as its bytes in network order, and the port. -/
inductive ShimAddr where
  /-- An IPv4 address and a port. -/
  | v4 (ip : List Nat) (port : UInt16)
  /-- An IPv6 address and a port. -/
  | v6 (ip : List Nat) (port : UInt16)
  deriving DecidableEq, Repr

namespace ShimAddr

/-- The address bytes have the length of their family. -/
def Valid : ShimAddr → Prop
  | .v4 ip _ => ip.length = 4
  | .v6 ip _ => ip.length = 16

/-- The bytes the shim reads: the family, the IP bytes, the port. -/
def encode : ShimAddr → List Nat
  | .v4 ip port => 4 :: ip ++ bytes16 port
  | .v6 ip port => 6 :: ip ++ bytes16 port

/-- Read the shim's bytes. `none` for a family byte that names no
family, and for a length that does not fit the family. -/
def decode? : List Nat → Option ShimAddr
  | 4 :: rest =>
    if rest.length = 6 then
      match rest.drop 4 with
      | [hi, lo] => some (.v4 (rest.take 4) (be16 hi lo))
      | _ => none
    else none
  | 6 :: rest =>
    if rest.length = 18 then
      match rest.drop 16 with
      | [hi, lo] => some (.v6 (rest.take 16) (be16 hi lo))
      | _ => none
    else none
  | _ => none

/-- The IP bytes and the port bytes of one family, read back. -/
private theorem split (n : Nat) (ip : List Nat) (port : UInt16) (h : ip.length = n) :
    (ip ++ bytes16 port).length = n + 2 ∧ (ip ++ bytes16 port).take n = ip ∧
      (ip ++ bytes16 port).drop n = bytes16 port := by
  subst h
  refine ⟨?_, ?_, ?_⟩
  · simp [bytes16]
  · simp
  · simp

/-- The round trip: every valid address reads back from its bytes. -/
theorem decode_encode (a : ShimAddr) (h : a.Valid) : decode? a.encode = some a := by
  cases a with
  | v4 ip port =>
    obtain ⟨hl, ht, hd⟩ := split 4 ip port h
    -- `hl` decides the length test, so `↓reduceIte` takes its branch.
    simp only [encode, decode?, List.cons_append, hl, ↓reduceIte, hd, ht]
    simp [bytes16, be16Bytes16]
  | v6 ip port =>
    obtain ⟨hl, ht, hd⟩ := split 16 ip port h
    simp only [encode, decode?, List.cons_append, hl, ↓reduceIte, hd, ht]
    simp [bytes16, be16Bytes16]

/-- A family byte that names no family reads as no address. -/
example : decode? [5, 127, 0, 0, 1, 0, 80] = none := by decide

/-- An IPv4 address with one port byte too few reads as no address. -/
example : decode? [4, 127, 0, 0, 1, 0] = none := by decide

end ShimAddr

/-! ## The socket address -/

/-- The shim's form of a socket address. -/
def shimOf : Std.Net.SocketAddress → ShimAddr
  | .v4 a => .v4 (a.addr.octets.toList.map (·.toNat)) a.port
  | .v6 a => .v6 (a.addr.segments.toList.flatMap bytes16) a.port

/-- The socket address of the shim's form. `none` when the IP bytes do
not fit the family. -/
def socketOf? : ShimAddr → Option Std.Net.SocketAddress
  | .v4 [a, b, c, d] port =>
    some (.v4 ⟨Std.Net.IPv4Addr.ofParts (UInt8.ofNat a) (UInt8.ofNat b) (UInt8.ofNat c)
      (UInt8.ofNat d), port⟩)
  | .v6 ip port =>
    match segments? ip with
    | some [s0, s1, s2, s3, s4, s5, s6, s7] =>
      some (.v6 ⟨Std.Net.IPv6Addr.ofParts s0 s1 s2 s3 s4 s5 s6 s7, port⟩)
    | _ => none
  | _ => none

/-- The shim's bytes of a socket address. -/
def toShim (sa : Std.Net.SocketAddress) : ByteArray :=
  ⟨((shimOf sa).encode.map UInt8.ofNat).toArray⟩

/-- The socket address of the shim's bytes. `none` for bytes that name
no address. -/
def ofShim? (b : ByteArray) : Option Std.Net.SocketAddress :=
  (ShimAddr.decode? (b.toList.map (·.toNat))).bind socketOf?

/-! ## The socket's own address -/

/-- The address at which a socket bound to `sa` receives its own
datagram: `sa`, with an unspecified IP (`0.0.0.0`, `::`) replaced by the
loopback of its family, since no datagram goes to an unspecified
address. The endpoint wakes its reader this way (`Quic/Loop.lean`,
`stopReading`). -/
-- TODO(lean v4.36): remove with the workaround (`stopReading`), and its
-- three checks in `Tests/Quic.lean`.
def selfAddress : Std.Net.SocketAddress → Std.Net.SocketAddress
  | .v4 a =>
    if a.addr = Std.Net.IPv4Addr.ofParts 0 0 0 0 then
      .v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, a.port⟩
    else .v4 a
  | .v6 a =>
    if a.addr = Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 0 then
      .v6 ⟨Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0 0 1, a.port⟩
    else .v6 a

/-! ## The multiaddr -/

/-- The socket address of a `quic-v1` multiaddr. `none` for every other
shape. -/
def socketAddress? (m : Multiaddr) : Option Std.Net.SocketAddress :=
  match m.components with
  | [⟨.«ip4», ip⟩, ⟨.«udp», [hi, lo]⟩, ⟨.«quic-v1», []⟩] => socketOf? (.v4 ip (be16 hi lo))
  | [⟨.«ip6», ip⟩, ⟨.«udp», [hi, lo]⟩, ⟨.«quic-v1», []⟩] => socketOf? (.v6 ip (be16 hi lo))
  | _ => none

/-- True when the address is a `quic-v1` multiaddr. The answer comes
from the shape alone, as `Streams.Transport.handles` asks, and `dial`
and `listen` decide through the same function. -/
def handles (m : Multiaddr) : Bool :=
  (socketAddress? m).isSome

/-- The `quic-v1` multiaddr of a socket address. The components always
pass the multiaddr check, since the sizes of `ip4`, `ip6`, and `udp`
hold by construction, so the `none` arm cannot occur. -/
def multiaddrOf (sa : Std.Net.SocketAddress) : Option Multiaddr :=
  let ip : Component := match sa with
    | .v4 a => ⟨.«ip4», a.addr.octets.toList.map (·.toNat)⟩
    | .v6 a => ⟨.«ip6», a.addr.segments.toList.flatMap bytes16⟩
  Multiaddr.ofComponents? [ip, ⟨.«udp», bytes16 sa.port⟩, ⟨.«quic-v1», []⟩]

end Quic
