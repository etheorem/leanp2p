import Conc

/-!
# Mock of `net/streams`

The frozen surface of the connection layer (ARCHITECTURE §4.7), until
W4.1 merges. The session of `Yamux/Session.lean` reads and writes
through `Connection` and serves `Stream` values; this module declares
exactly those two types, plus the address and the per-stream error.

The types follow the package document: `read` answers `none` at the
end of the stream, a fault is `IO.Error`, and a stream's `read` reports
the muxer's own error (a reset, or a closed session). When W4.1 merges,
the import and the namespace move to `Streams` and this module goes
away; the ledger on issue #25 records that connection.
-/

set_option autoImplicit false


namespace Yamux.Mock.Streams

/-- The monad of the operations that can park. -/
abbrev Async := Conc.Async

/-- A peer address. The session only carries it through. -/
structure Multiaddr where
  /-- The wire bytes of the address. -/
  bytes : List Nat
  deriving Repr, DecidableEq, BEq, Hashable

/-- Why a stream operation failed. -/
inductive Error where
  /-- The stream or the session is closed. -/
  | closed
  /-- The peer or the application reset the stream. -/
  | reset
  deriving Repr, DecidableEq, BEq, Hashable

/-- One byte stream in both directions between two peers. -/
structure Connection where
  /-- The next chunk of bytes, of any length above zero. -/
  read : Async (Option ByteArray)
  /-- Write the bytes, and return when the transport took them. -/
  write : ByteArray → Async Unit
  /-- Close both directions. -/
  close : IO Unit
  /-- The address of our end. -/
  localAddr : Multiaddr
  /-- The address of the peer's end. -/
  remoteAddr : Multiaddr

/-- The application view of one muxed stream. -/
structure Stream where
  /-- The next chunk; `none` at the end of the stream. -/
  read : Async (Except Error (Option ByteArray))
  /-- Write the bytes, and return when they are on the wire. -/
  write : ByteArray → Async (Except Error Unit)
  /-- Close our write direction. -/
  close : Async Unit
  /-- Stop both directions. -/
  reset : Async Unit

end Yamux.Mock.Streams
