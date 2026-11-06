import Conc
import Streams.Constants
import Multiformats.Multiaddr

/-!
# Connections, listeners, and the `Transport` seam

A `Connection` is one byte stream in both directions between two
peers. Every layer above reads and writes through it: the negotiation,
the security handshake, and the muxer. A `Listener` supplies the
connections that peers dial. A `Transport` is the seam (ARCHITECTURE
§3.1) that dials and listens.

The address picks the transport before any negotiation runs, so the
seam carries no protocol id. `handles` tells whether an address belongs
to the transport. Two values fill the seam: the in-memory sim of
`Streams.Sim`, and TCP (`Streams.Tcp`).

Each operation fails through one channel of §3.5:

* `read` answers `none` at the end of the stream: the peer sent a FIN
  or an RST, or our own `close` woke the read. A FIN and an RST both
  tell that the peer has finished, the end-of-stream row of §3.5 (the
  package ARCHITECTURE, "Decisions", the peer's reset).
* A fault throws `IO.Error`: a socket error of our own system, such as
  a network that is down, or a write to a closed connection.

A write that fails tears the connection down (§4.7). The local read
then sees EOF, and the peer gets a FIN, or an RST when a write is in
flight. Each transport value keeps this
rule, so a caller never holds a connection that is half closed.

`Connection` holds operations and no state. The state lives in the
transport value behind the fields, so the seam shows no `IO.Ref`
(§3.1).

`Multiaddr` comes from `codec/multiformats`.
-/

set_option autoImplicit false

namespace Streams

open Conc Multiformats

/-- One byte stream in both directions between two peers. -/
structure Connection where
  /-- The next chunk of bytes, of any length above zero. `none` at the
  end of the stream, a FIN or an RST from the peer. A read can split or
  join the writes of the peer, so no caller can use the write
  boundaries. -/
  read : Async (Option ByteArray)
  /-- Write the bytes, and return when the transport has taken them. A
  failed write throws `IO.Error`, and the transport tears the
  connection down before the throw. A fault tells nothing about
  delivery: the bytes can be at the peer in full, in part, or not at
  all, as with a POSIX `write` that fails. A `close` during the write
  also gives the write a fault. A layer that must know what arrived
  needs an answer from the peer. -/
  write : ByteArray → Async Unit
  /-- Close both directions: send a FIN to the peer, and wake a parked
  `read` of our own with `none`. A second close does nothing. -/
  close : IO Unit
  /-- The address of our end. -/
  localAddr : Multiaddr
  /-- The address of the peer's end. -/
  remoteAddr : Multiaddr

/-- A source of the connections that peers dial to one address. -/
structure Listener where
  /-- The address that the listener serves. -/
  addr : Multiaddr
  /-- The next dialed connection. `none` when the listener is closed:
  `close` wakes a parked accept. -/
  accept : Async (Option Connection)
  /-- Stop the listener. Every parked `accept` wakes with `none`. A
  second close does nothing. -/
  close : IO Unit
  /-- Wait until every task of the listener ends. The owner calls
  it after `close` (ARCHITECTURE §4.1, rule 2; §3.1, lifecycle). -/
  join : Async Unit

/-- The transport seam: which addresses it serves, how to reach one,
and how to serve one.

A multiaddr names its own protocol stack (the addressing spec,
`vendor/specs/addressing/README.md`), so the address picks the
transport. A consumer that holds more than one transport (ARCHITECTURE
§3.1) asks each one `handles`. The package ARCHITECTURE ("Checked
against the implementations") gives the reference that asks the same
question. -/
structure Transport where
  /-- True when this transport dials and listens on the address. The
  answer comes from the shape of the address alone. It opens no
  socket, and it tells nothing about a listener at the address. `dial`
  and `listen` throw a fault for an address that `handles` refuses. -/
  handles : Multiaddr → Bool
  /-- Dial the address. `none` when nothing listens there. Every other
  failure is a fault. -/
  dial : Multiaddr → Async (Option Connection)
  /-- Listen on the address. An address in use is a fault. -/
  listen : Multiaddr → Async Listener

namespace Connection

/-- Read until exactly `n` bytes have arrived after `pending`, the bytes
that the caller holds already. The answer is the `n` bytes, and the
bytes read past them. `none` when the stream ends first. The bytes read
before the end are lost with the stream.

The over-read is a part of the answer, so no byte strands inside the
call (§4.7, "No reader strand"). The caller gives it to the next read
at the same level, usually through a `BufReader`.

The call allocates up to `n` bytes and one chunk more. A caller that
reads a length from the wire caps it first (§5.1). -/
def readExactly (c : Connection) (n : Nat) (pending : ByteArray := .empty) :
    Async (Option (ByteArray × ByteArray)) := do
  let mut acc := pending
  -- Each pass reads one chunk. The first append copies `pending` when
  -- the caller still holds it. After that the loop is the one holder
  -- of `acc`, and a `ByteArray` with one holder grows in place under
  -- `++` with capacity doubling, so each byte is copied a bounded
  -- number of times.
  while acc.size < n do
    match ← c.read with
    | some chunk => acc := acc ++ chunk
    | none => return none
  return some (acc.extract 0 n, acc.extract n acc.size)

/-- Close, and drop a fault of the close. A close fault leaves the
caller nothing to do, since the connection is gone either way. The
deadline below needs a close that cannot throw (`Conc.withinDeadline`). -/
def closeQuietly (c : Connection) : BaseIO Unit :=
  discard c.close.toBaseIO

/-- Run an unauthenticated phase of `c` against the deadline of §5.4.
At the expiry, the deadline closes the connection. The close wakes the
read that the phase parks on, the phase ends, and the answer is
`.error .deadlineExpired`.

The caller wraps only the phase before the authentication. An
authenticated connection with no traffic never expires. A phase that
ends with a value after the expiry gives the value to `release`
(`Conc.withinDeadline`). A handshake that built a session over `c` frees
the session there. -/
def withinUnauthDeadline {α : Type} (c : Connection) (clock : Clock) (phase : Async α)
    (release : α → BaseIO Unit := fun _ => pure ()) : Async (Except Conc.Error α) :=
  withinDeadline clock unauthDeadlineMs c.closeQuietly phase release

end Connection

end Streams
