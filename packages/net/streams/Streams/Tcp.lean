import Std.Async.TCP
import StreamsShim
import Streams.Conn

/-!
# The TCP transport

TCP is the production value of the `Transport` seam (ARCHITECTURE
§3.1), and the transport the consensus layer runs on (§8). This module
is the only one of the stack that touches the socket API of the
toolchain (§9, delta 7), so a toolchain move breaks one file.

## Which layer it binds

`Std.Async.TCP` wraps the libuv sockets of `Std.Internal.UV.TCP`, and
turns each native promise into an `Async` value at once. The close
discipline needs the promise itself (below), so this module calls the
native socket, which the public wrapper re-exports, and awaits each
promise through `Async.ofPromise`.

## The close discipline (§4.7)

libuv drops a cancelled promise. A task parked on it would never wake,
against PRINCIPLES 3.1. So a close never stops at the cancel: it first
resolves the promise of every parked operation itself, and only then
lets libuv drop its reference (`cancelRecv`, `cancelAccept`). The
first resolve of a promise wins, and a later one does nothing
(`IO.Promise.resolve`), so the close and libuv can both resolve one
promise in either order.

* `Connection.close` resolves the parked read with EOF and every write
  in flight with a fault, stops the reads, and ends the connection
  toward the peer: a FIN, or an RST when a write is in flight. A
  second close does nothing.
* A failed write, or a failed read, runs the same teardown, then throws.
  The local read sees EOF from then on, and the peer gets the FIN or
  the RST by the same rule.
* A read that meets the peer's reset runs the same teardown, and
  answers EOF (below, "The peer's reset").
* `Listener.close` resolves the parked accept, so it wakes with `none`.

## Releasing the handle

The native socket has no close call: the runtime closes the handle when
the last reference to the socket goes. A listener whose handle stays
open still listens in the kernel, so a peer's connect completes and
then waits for an accept that never comes, and the port stays bound.
So each connection and each listener keeps its socket in its state
cell, and no closure holds a copy. `close` takes the socket out, and
with it the last reference: a closed listener refuses the next connect,
and its port is free. A connection hands its socket to the continuation
of `shutdown` instead, so the handle closes once the FIN is out.

The cell is not the only holder. Every pending connect, write, and
shutdown request of the runtime holds a reference too
(`vendor/lean4/src/runtime/uv/tcp.cpp`), and a write to a peer that
stops reading never completes. Its socket, and the descriptor, would then live
forever, and a peer could exhaust our descriptors that way. The runtime
offers no call that ends such a request, so the teardown calls
`StreamsShim.abort` when a write is in flight: the kernel fails the
pending requests, they drop their references, and the runtime closes
the handle. The peer gets an RST. A dial that outlives its deadline
aborts its connect the same way. With no write in flight, the teardown
takes the graceful path, `shutdown` and the FIN.

## The peer's reset

A peer ends a TCP connection with a FIN or with an RST. Both say that
the peer has finished, the end-of-stream row of §3.5. A fault is the
other row: "the system failed". So a read that meets the peer's RST
answers `none`, as a read at the FIN does. The peer may use RST as its
normal close, and this transport does so itself when its teardown
aborts. The package ARCHITECTURE ("Decisions", the peer's reset) cites
the implementations that close and read the same way.

The runtime reports the reset as `resourceVanished` with the errno
`ECONNRESET`. The same constructor carries `EPIPE`, `ENETDOWN`, and
`ENETRESET`, which stay faults, so the read compares the code with the
platform's value (`StreamsShim.econnreset`). A frame that the RST cuts
short ends as `none` mid-frame, as one cut by a FIN does (the package
ARCHITECTURE, `Framing`).

## Deadlines (§5.4)

A dial waits on its connect for at most `unauthDeadlineMs` on the
transport's clock. On expiry the deadline resolves the connect promise
itself, by the rule above, and the dial throws `timeExpired`. The phases
after the connect, up to authentication, run under
`Connection.withinUnauthDeadline` in the layers that own them.

## The address forms

A TCP multiaddr has exactly two components. The `ip4` value is 4 bytes,
the `ip6` value is 16 bytes, and the `tcp` value is a 2-byte big-endian
port (`vendor/multiaddr/protocols.csv`). Every other shape is not a TCP
address for this transport. A `/p2p` suffix belongs to the host, which
strips it before the dial.

## Theorems

The byte arithmetic of the mapping is pure, so its round trips are
theorems: a port goes to its two bytes and back, and the 16 bytes of an
IPv6 value go to their 8 segments and back.
-/

set_option autoImplicit false

namespace Streams.Tcp

open Conc Multiformats

/-- The native socket. -/
abbrev Socket := Std.Internal.UV.TCP.Socket

/-! ## Addresses -/

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

/-- True when the address has a shape that `socketAddress?` takes.
`dial` and `listen` decide through the same function, so the two
answers cannot disagree. -/
def handles (m : Multiaddr) : Bool :=
  (socketAddress? m).isSome

/-! ## Faults -/

/-- The fault of an address that is not a TCP multiaddr. -/
private def notTcp (m : Multiaddr) : IO.Error :=
  .invalidArgument none 0 s!"tcp: {m.describe} is not /ip4|ip6/<addr>/tcp/<port>"

/-- The fault of an operation on a closed connection, and the answer
that `close` gives the writes in flight. -/
private def closedError : IO.Error :=
  .resourceVanished 0 "tcp: the connection is closed"

/-- The fault of a dial whose connect outlived the deadline. -/
private def dialExpired : IO.Error :=
  .timeExpired 0 "tcp: the connect outlived the unauthenticated deadline"

/-- The error is the peer's reset (module doc, "The peer's reset"). -/
private def peerReset : IO.Error → Bool
  | .resourceVanished code _ => code == StreamsShim.econnreset ()
  | _ => false

/-- The multiaddr of a socket address, or a fault. -/
private def addrOf (sa : Std.Net.SocketAddress) : IO Multiaddr := do
  match multiaddrOf sa with
  | some m => return m
  | none => throw <| IO.userError s!"tcp: {sa} has no multiaddr"

/-- Wait for a native promise. A promise that libuv drops unresolved
answers a fault; the close discipline makes sure no promise that a task
waits on is dropped that way. -/
private def await {α : Type} (p : IO.Promise (Except IO.Error α)) :
    Async (Except IO.Error α) :=
  try .ok <$> Std.Async.Async.ofPromise (pure p)
  catch e => pure (.error e)

/-! ## Connections -/

/-- The parks of one connection, which `close` must reach, and the
socket itself. -/
private structure ConnState where
  /-- The socket; `none` after the teardown. The cell holds the one
  reference that outlives an operation, so the teardown releases the
  handle by taking it out (module doc, "Releasing the handle"). -/
  sock : Option Socket
  /-- The promise of the parked read, when a read is parked. -/
  reading : Option (IO.Promise (Except IO.Error (Option ByteArray)))
  /-- The promises of the writes in flight, each with a number. -/
  writing : List (Nat × IO.Promise (Except IO.Error Unit))
  /-- The next write number. -/
  nextWrite : Nat

/-- Send the FIN, and release the handle once the FIN is out. The
continuation on the shutdown promise holds the last reference to the
socket, so the runtime closes the handle only after the shutdown
completed; a release before it could close the descriptor first. The
teardown calls it only with no write in flight, so the shutdown
completes at once (module doc, "Releasing the handle"). -/
private def finish (sock : Socket) : BaseIO Unit := do
  match ← sock.shutdown.toBaseIO with
  | .ok done =>
    -- `cancelRecv` is idempotent, and its call makes the closure hold
    -- `sock` until the task runs.
    discard <| IO.mapTask (t := done.result?) fun _ => sock.cancelRecv
  | .error _ => pure ()

/-- The connection over a connected socket. -/
private def connection (sock : Socket) : IO Connection := do
  let localAddr ← addrOf (← sock.getSockName)
  let remoteAddr ← addrOf (← sock.getPeerName)
  -- From here the socket lives in the cell only: no closure below names
  -- `sock`, so taking it out of the cell releases it.
  let state : OnceRef ConnState ←
    OnceRef.new { sock := some sock, reading := none, writing := [], nextWrite := 0 }

  -- The teardown: wake every park, then let libuv drop its references,
  -- then send the FIN and release the handle. One atomic step takes the
  -- socket and the parks, so a second teardown finds none.
  let shut : BaseIO Unit := do
    let (sock?, reading, writing) ← state.updateGet fun s =>
      ((s.sock, s.reading, s.writing), { s with sock := none, reading := none, writing := [] })
    let some sock := sock? | return
    if let some p := reading then p.resolve (.ok none)
    for (_, p) in writing do p.resolve (.error closedError)
    discard sock.cancelRecv.toBaseIO
    -- A write in flight may never complete (a peer that stops reading),
    -- and it holds the socket; so does a shutdown queued behind it. The
    -- abort fails it, and the handle closes. With no write in flight,
    -- the graceful path sends the FIN.
    if writing.isEmpty then finish sock else StreamsShim.abort sock

  let read : Async (Option ByteArray) := do
    let some sock := (← (state.get : BaseIO ConnState)).sock | return none
    let p ← sock.recv? tcpReadChunk.toUInt64
    -- Register the park, unless a close came first; then the read
    -- resolves its own promise, as the close would have.
    let parked ← (state.updateGet fun s =>
      if s.sock.isNone then (false, s) else (true, { s with reading := some p }) : BaseIO Bool)
    if !parked then
      p.resolve (.ok none)
      discard sock.cancelRecv.toBaseIO
    -- Park: libuv resolves the promise with bytes, EOF, or an error,
    -- and `close` resolves it with EOF.
    let r ← await p
    state.update fun s => { s with reading := none }
    match r with
    | .ok chunk => return chunk
    | .error e =>
      shut
      -- The peer's reset is its end (module doc, "The peer's reset").
      if peerReset e then return none
      throw e

  let write (bytes : ByteArray) : Async Unit := do
    let some sock := (← (state.get : BaseIO ConnState)).sock | throw closedError
    if bytes.isEmpty then return
    let p ← sock.send #[bytes]
    let id ← (state.updateGet fun s =>
      if s.sock.isNone then (none, s)
      else (some s.nextWrite,
        { s with writing := (s.nextWrite, p) :: s.writing, nextWrite := s.nextWrite + 1 }) :
      BaseIO (Option Nat))
    if id.isNone then p.resolve (.error closedError)
    -- Park: libuv resolves the promise when the bytes are sent, and
    -- `close` resolves it with a fault.
    let r ← await p
    if let some id := id then
      state.update fun s => { s with writing := s.writing.filter (·.1 != id) }
    match r with
    | .ok () => return
    | .error e =>
      -- A failed write tears the connection down before the throw.
      shut
      throw e

  return { read, write, close := do shut, localAddr, remoteAddr }

/-! ## Dial and listen -/

/-- Dial `m`. `none` when nobody listens there (the connect is refused:
libuv reports `ECONNREFUSED` as `noSuchThing`). The connect waits for at
most `unauthDeadlineMs` on `clock`, and an expiry throws
`timeExpired`. -/
def dial (clock : Clock) (m : Multiaddr) : Async (Option Connection) := do
  let some sa := socketAddress? m | throw (notTcp m)
  let sock ← Std.Internal.UV.TCP.Socket.new
  let p ← sock.connect sa
  -- On expiry the deadline resolves the connect promise itself, so the
  -- park below wakes (the close discipline), and aborts the connect,
  -- whose request would hold the socket until the kernel gives up on
  -- the SYN.
  let expire : BaseIO Unit := do
    p.resolve (.error dialExpired)
    StreamsShim.abort sock
  match ← withinDeadline clock unauthDeadlineMs expire (await p) with
  | .error _ => throw dialExpired
  | .ok (.ok ()) => return some (← connection sock)
  | .ok (.error (.noSuchThing ..)) => return none
  | .ok (.error e) => throw e

/-- The parks of one listener, which `close` must reach, and the
socket itself. -/
private structure ListenState where
  /-- The listening socket; `none` after `close`. The cell holds the one
  reference that outlives an accept, so `close` releases the handle by
  taking it out: the kernel stops listening, and the port is free. -/
  sock : Option Socket
  /-- The promise of the parked accept, when an accept is parked. -/
  accepting : Option (IO.Promise (Except IO.Error Socket))

/-- Listen on `m`. A port of 0 lets the system pick one, and the
listener's `addr` names the port it got. -/
def listen (m : Multiaddr) : Async Listener := do
  let some sa := socketAddress? m | throw (notTcp m)
  let sock ← Std.Internal.UV.TCP.Socket.new
  sock.bind sa
  sock.listen tcpBacklog.toUInt32
  let addr ← addrOf (← sock.getSockName)
  -- From here the socket lives in the cell only, as in `connection`.
  let state : OnceRef ListenState ← OnceRef.new { sock := some sock, accepting := none }

  let shut : BaseIO Unit := do
    let (sock?, accepting) ← state.updateGet fun s =>
      ((s.sock, s.accepting), { sock := none, accepting := none })
    let some sock := sock? | return
    if let some p := accepting then p.resolve (.error closedError)
    discard sock.cancelAccept.toBaseIO
    -- `sock` goes out of scope here with the last reference, and the
    -- runtime closes the handle.

  -- One accept: the next connection, `none` once closed. A peer that
  -- resets between the accept and the address lookup is dropped, and
  -- the loop takes the next one.
  let accept : Async (Option Connection) := do
    repeat
      let some sock := (← (state.get : BaseIO ListenState)).sock | return none
      let p ← sock.accept
      let parked ← (state.updateGet fun s =>
        if s.sock.isNone then (false, s) else (true, { s with accepting := some p }) : BaseIO Bool)
      if !parked then
        p.resolve (.error closedError)
        discard sock.cancelAccept.toBaseIO
      -- Park: libuv resolves the promise with a socket, and `close`
      -- resolves it with a fault.
      let r ← await p
      state.update fun s => { s with accepting := none }
      match r with
      | .ok client =>
        match ← (connection client).toBaseIO with
        | .ok c => return some c
        | .error _ => continue
      | .error e =>
        if (← (state.get : BaseIO ListenState)).sock.isNone then return none
        throw e
    return none

  return {
    addr
    accept
    close := do shut
    -- The listener runs no task of its own.
    join := pure () }

/-- The TCP value of the `Transport` seam. `clock` bounds the connect
of each dial (§5.4); production code passes `Clock.system`, the
default. -/
def transport (clock : Clock := Clock.system) : Transport where
  handles := handles
  dial := dial clock
  listen := listen

end Streams.Tcp
