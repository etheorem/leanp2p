import Std.Net.Addr
import Streams.Conn

/-!
# The TCP transport

TCP is the production value of the `Transport` seam (ARCHITECTURE §3.1),
and the transport that the consensus layer runs on (§8). This module is
the only one of the stack that can touch the socket API of the
toolchain, `Std.Async.TCP` (§9, delta 7), so a toolchain move breaks
one file.

## The stub of unit 1

Unit 1 (root W4.1) gives the seam its TCP value as a stub. The value
has the full address mapping:

* `socketAddress?` reads the endpoint out of a TCP multiaddr,
  `/ip4/<addr>/tcp/<port>` or `/ip6/<addr>/tcp/<port>`.
* `multiaddrOf` writes a socket address back as a multiaddr, for the
  `localAddr` and the `remoteAddr` of a connection.
* `handles` answers `true` for the shapes that `socketAddress?` takes.

`dial` and `listen` check the address, and then throw. The sockets, the
close discipline of §4.7, and the deadline wiring come with unit 2
(root W4.2). So a caller can put `Tcp.transport` in its transport list
now, and the suites above run on the sim (PRINCIPLES 1.4).

## The address forms

A TCP multiaddr has exactly two components. The `ip4` value is 4 bytes,
the `ip6` value is 16 bytes, and the `tcp` value is a 2-byte big-endian
port (`vendor/multiaddr/protocols.csv`). Every other shape is not a TCP
address for this transport.

## Theorems

The byte arithmetic of the mapping is pure, so its round trips are
theorems: a port goes to its two bytes and back, and the 16 bytes of an
IPv6 value go to their 8 segments and back.
-/

set_option autoImplicit false

namespace Streams.Tcp

open Conc Streams.Mock.Multiformats

/-- The big-endian 16-bit value of two bytes. -/
def be16 (hi lo : Nat) : UInt16 :=
  UInt16.ofNat (hi * 256 + lo)

/-- The two big-endian bytes of a 16-bit value. -/
def bytes16 (v : UInt16) : List Nat :=
  [v.toNat / 256, v.toNat % 256]

/-- The 8 big-endian 16-bit segments of a 16-byte IPv6 value. -/
def segments? : List Nat → Option (List UInt16)
  | [] => some []
  | hi :: lo :: rest => (segments? rest).map (be16 hi lo :: ·)
  | [_] => none

/-- A 16-bit value survives the trip through its two bytes. -/
theorem be16Bytes16 (v : UInt16) : be16 (v.toNat / 256) (v.toNat % 256) = v := by
  have h : v.toNat / 256 * 256 + v.toNat % 256 = v.toNat := by omega
  simp only [be16, h, UInt16.ofNat_toNat]

/-- The two bytes of a 16-bit value are bytes. -/
theorem ltOfMemBytes16 {v : UInt16} {x : Nat} (h : x ∈ bytes16 v) : x < 256 := by
  have := v.toNat_lt
  simp only [bytes16, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

/-- Segments survive the trip through their bytes. -/
theorem segments?FlatMapBytes16 (l : List UInt16) :
    segments? (l.flatMap bytes16) = some l := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.flatMap_cons, bytes16, List.cons_append, List.nil_append, segments?, ih,
      Option.map_some, be16Bytes16]

/-- The bytes of the segments: two for each segment. -/
theorem lengthFlatMapBytes16 (l : List UInt16) : (l.flatMap bytes16).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, bytes16, List.length_cons,
      List.length_nil]
    omega

/-- The socket address of a TCP multiaddr. `none` for every other
shape. -/
def socketAddress? (m : Multiaddr) : Option Std.Net.SocketAddress :=
  match m.components with
  | [⟨.«ip4», [a, b, c, d]⟩, ⟨.«tcp», [hi, lo]⟩] =>
    let ip := Std.Net.IPv4Addr.ofParts (UInt8.ofNat a) (UInt8.ofNat b) (UInt8.ofNat c) (UInt8.ofNat d)
    some (.v4 ⟨ip, be16 hi lo⟩)
  | [⟨.«ip6», v⟩, ⟨.«tcp», [hi, lo]⟩] =>
    match segments? v with
    | some [s0, s1, s2, s3, s4, s5, s6, s7] =>
      some (.v6 ⟨Std.Net.IPv6Addr.ofParts s0 s1 s2 s3 s4 s5 s6 s7, be16 hi lo⟩)
    | _ => none
  | _ => none

/-- The multiaddr of a socket address: `/ip4/…/tcp/…` or `/ip6/…/tcp/…`.
The components always pass the multiaddr check, since the sizes of
`ip4`, `ip6`, and `tcp` hold by construction. So the `none` arm cannot
occur. `ofComponents?` is what gives the address its proof field. -/
def multiaddrOf (sa : Std.Net.SocketAddress) : Option Multiaddr :=
  let ip : Component := match sa with
    | .v4 a => ⟨.«ip4», a.addr.octets.toList.map (·.toNat)⟩
    | .v6 a => ⟨.«ip6», a.addr.segments.toList.flatMap bytes16⟩
  Multiaddr.ofComponents? [ip, ⟨.«tcp», bytes16 sa.port⟩]

/-- True when the address has a shape that `socketAddress?` takes. -/
def handles (m : Multiaddr) : Bool :=
  (socketAddress? m).isSome

/-- The fault of an address that is not a TCP multiaddr. -/
private def notTcp (m : Multiaddr) : IO.Error :=
  .invalidArgument none 0 s!"tcp: {m.describe} is not /ip4|ip6/<addr>/tcp/<port>"

/-- The fault of every dial and every listen until unit 2. -/
private def notYet : IO.Error :=
  .unsupportedOperation 0 "tcp: the TCP transport comes with unit W4.2"

/-- The TCP value of the `Transport` seam: the stub of unit 1. Both
operations check the address, and then throw `notYet`. -/
def transport : Transport where
  handles := handles
  dial m := do
    if !handles m then throw (notTcp m)
    throw notYet
  listen m := do
    if !handles m then throw (notTcp m)
    throw notYet

end Streams.Tcp
