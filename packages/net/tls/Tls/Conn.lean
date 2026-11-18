import Conc
import Streams
import TlsNative
import Tls.Constants
import Tls.Error
import Tls.Context

/-!
# TLS 1.3 over a connection

`Tls.handshake` runs a TLS 1.3 handshake over a `Streams.Connection`,
and answers a `Secured`: a connection whose bytes travel in TLS
records, the peer's certificate, and the selected ALPN protocol.

## The engine and the bytes

The libssl session reads from one memory BIO and writes to another
(`TlsNative`). This module moves the bytes between the BIOs and the
connection: a connection read goes into the session, and the session's
output goes to the connection. So every byte that the negotiation or
the handshake read past its last message goes into the session too,
and the session decrypts it at the next read. The hand-over of root
§4.7 happens inside the engine, and `Secured` has no leftover to hand
on.

## The certificate check

The caller passes its check of the peer's certificate to `handshake`:
a pure function of the certificate's DER, `none` to accept and
`some reason` to refuse. libssl's verify callback runs it inside the
handshake, after the shim's own rule that the peer sent exactly one
certificate (the package ARCHITECTURE, "The certificate check"). A
refusal fails the handshake with `Error.peerCertificate reason`, and
libssl sends the alert `bad_certificate`, as Go's `crypto/tls` does
when its `VerifyPeerCertificate` fails. So no `Secured` exists for a refused
peer. A client can still finish its handshake before the server has
checked the client's certificate (the TLS spec's "Note for clients"):
the server's alert then fails the client's first read.

## The order of the records

The secure read and the secure write run on two tasks. The shim's
mutex makes each call atomic, but the bytes of two calls reach the
connection through two writes, and a reordered pair breaks the record
sequence. So one write token orders the output: a task drains the
session's output and writes it to the connection only while it holds
the token. The output BIO is first in, first out, so the bytes reach
the connection in the order the session produced them.

The token is a `Chan Unit` of one slot, which holds the token when no
task does. `close` closes the channel, which wakes every task that
parks on it (PRINCIPLES 3.1).

A read that succeeds leaves no output, so only writers use the token.
libssl answers a peer's KeyUpdate before its own next application data
record (`ssl3_write_bytes`, `ssl/record/rec_layer_s3.c`), as RFC 8446
§4.6.3 allows ("prior to sending its next Application Data record").
Session tickets are off, and the read of a `close_notify` sends
nothing. So a held token always means a write in flight. A read that
fails is the one read with output, its fatal alert ("Failures").

## The close

`close` sends `close_notify`, as RFC 8446 §6.1 asks, with Go's two
rules (`crypto/tls`, `conn.go`, `Close` and `closeNotify`). A close
while a write is in flight breaks that write and sends no alert, so
the alert never lands between the records of one write: the close
takes the token without a wait, and a held token is a write in
flight. The write of the alert is bounded by `closeNotifyMs`, 5
seconds.

`abort` closes with no alert. It is the close of a fatal error that
the caller finds after the handshake, which RFC 8446 §6.2 asks to
close "without sending or receiving any additional data". libssl has
no call that sends an arbitrary alert after the handshake, so the
alert that §6.2 says the close SHOULD send stays unsent.

## Failures

A failed record is a protocol error (root §3.5). The secure read
records it, closes the connection, and answers `none`, so the layer
above sees an orderly end. `Secured.join` answers the recorded error.
A failed write records the error, closes the connection, and throws,
as `Connection.write` requires. A failed read or write first sends the
fatal alert that libssl queued for it (RFC 8446 §6.2, "it SHOULD send
an appropriate fatal alert"). The read sends it only when no write
holds the token, so the alert never lands inside a write.

The end of the connection follows Go's rule (`readRecordOrCCS`): an
end at a record boundary is an orderly end, even with no
`close_notify`, and an end inside a record is a failed record.
-/

set_option autoImplicit false

namespace Tls

open Conc Streams

/-- A connection after the TLS handshake. -/
structure Secured where
  /-- The secure connection: `read` answers plaintext, and `write`
  sends TLS records. The addresses are those of the connection under
  it. -/
  connection : Connection
  /-- The peer's certificate, as DER, which the caller's check
  accepted. -/
  peerCertificate : ByteArray
  /-- The ALPN protocol that the handshake selected; empty when the
  peer used no ALPN. -/
  alpn : String
  /-- Send a TLS 1.3 KeyUpdate that asks the peer to update its keys
  too (RFC 8446 §4.6.3). It orders with the writes, and fails as a
  write fails. -/
  keyUpdate : Async Unit
  /-- Close with no alert: the close of a fatal error (RFC 8446 §6.2).
  The owner still calls `join`. -/
  abort : BaseIO Unit
  /-- Wait until the tasks of the connection have ended, and answer
  how it ended: `.ok` for an orderly end, the failed record otherwise.
  The owner calls it after `close` (root §3.1, "Lifecycle"). -/
  join : Async (Except Error Unit)

/-- Write the session's output to the connection, when it holds any.
The caller holds the write token. -/
private def flushOutput (s : TlsNative.Session) (raw : Connection) : Async Unit := do
  let out ← (TlsNative.drain s : IO ByteArray)
  if out.size > 0 then raw.write out

/-- Run the handshake to its end. Each step leaves its output in the
session, and the loop writes it before it reads more input, so the
peer's next message can come. The function is `partial`: it ends when
the handshake does, or when the connection ends, and no measure shows
that a peer ever sends the last message (CLAUDE.md, "`partial def`"). -/
private partial def handshakeLoop (s : TlsNative.Session) (raw : Connection) :
    Async (Except Error Unit) := do
  let code ← (TlsNative.handshakeStep s : IO UInt8)
  -- A failed step can still leave an alert for the peer.
  flushOutput s raw
  match code with
  | 0 => return .ok ()
  | 1 =>
    -- Park: the peer's next flight wakes it, and so does a close of the
    -- connection, by the peer or by the caller's deadline.
    match ← raw.read with
    | some b =>
      unless ← (TlsNative.feed s b : IO Bool) do
        return .error (.handshake (← (TlsNative.lastError s : IO String)))
      handshakeLoop s raw
    | none => return .error .closed
  | 3 => return .error (.peerCertificate (← (TlsNative.lastError s : IO String)))
  | _ => return .error (.handshake (← (TlsNative.lastError s : IO String)))

/-- The state the secure connection's operations share. -/
private structure Shared where
  session : TlsNative.Session
  raw : Connection
  /-- The write token (the module doc, "The order of the records"). -/
  token : Chan Unit
  /-- The first failure of a record. -/
  failure : OnceRef (Option Error)
  /-- Set by the first `close` or `abort`. -/
  closing : OnceRef Bool
  /-- The task that sends the `close_notify` alert. -/
  tasks : TaskSet
  clock : Clock

/-- Record the first failure, and close the connection. -/
private def Shared.fail (sh : Shared) (e : Error) : BaseIO Unit := do
  sh.failure.update fun | none => some e | old => old
  sh.raw.closeQuietly

/-- Send the fatal alert that a failed read left in the session's
output, when no write holds the token (the module doc, "Failures").
The connection closes right after, so a failed send changes nothing,
and the call drops its error. -/
private def Shared.sendReadAlert (sh : Shared) : Async Unit := do
  let some () ← (sh.token.tryRecv : BaseIO (Option Unit)) | return
  try flushOutput sh.session sh.raw catch _ => pure ()
  discard <| (sh.token.trySend () : BaseIO Bool)

/-- The secure read: decrypt the next record, and read the connection
when the session needs more input. The function is `partial`, as the
read loops of `net/streams` are: it ends when a record is whole, or
when the connection ends. -/
private partial def Shared.read (sh : Shared) : Async (Option ByteArray) := do
  let r ← (TlsNative.read sh.session maxRecordPlaintext.toUSize : IO TlsNative.ReadRaw)
  match r.code with
  | 0 => return some r.bytes
  | 1 =>
    -- Park: the peer's next bytes wake it, and so does a close of the
    -- connection.
    match ← sh.raw.read with
    | some b =>
      unless ← (TlsNative.feed sh.session b : IO Bool) do
        sh.fail (.record (← (TlsNative.lastError sh.session : IO String)))
        return none
      sh.read
    | none =>
      -- The end of the connection (the module doc, "Failures"): an end
      -- inside a record is a failed record.
      if ← (TlsNative.partialRecord sh.session : IO Bool) then
        sh.fail (.record "the connection ended inside a TLS record")
      return none
  | 2 => return none
  | _ =>
    let d ← (TlsNative.lastError sh.session : IO String)
    sh.sendReadAlert
    sh.fail (.record d)
    return none

/-- One step that puts records in the session's output, under the
token: `step` encrypts, and the output then goes to the connection.
`what` names the step in the error of a failure, and a failure first
sends the alert libssl queued for it (the module doc, "Failures"). -/
private def Shared.underToken (sh : Shared) (what : String) (step : IO Bool) : Async Unit := do
  if ← (sh.closing.get : BaseIO Bool) then
    throw <| IO.userError s!"tls: {what} on a closed connection"
  -- Park: the release of the holder before wakes it, and so does
  -- `close`, which closes the token.
  let some () ← sh.token.recv
    | throw <| IO.userError s!"tls: {what} on a closed connection"
  try
    unless ← step do
      let d ← (TlsNative.lastError sh.session : IO String)
      try flushOutput sh.session sh.raw catch _ => pure ()
      sh.fail (.record d)
      throw <| IO.userError s!"tls: the {what} failed: {d}"
    flushOutput sh.session sh.raw
  finally discard <| (sh.token.trySend () : BaseIO Bool)

/-- Send the `close_notify` alert, then close the connection, by Go's
rules (the module doc, "The close"). The token is taken without a
wait: a held token is a write in flight, and the close then sends no
alert. -/
private def Shared.closeTask (sh : Shared) : Async Unit := do
  if let some () ← (sh.token.tryRecv : BaseIO (Option Unit)) then
    TlsNative.shutdown sh.session
    let out ← (TlsNative.drain sh.session : IO ByteArray)
    if out.size > 0 then
      -- The deadline's close wakes a write that a stalled peer parks.
      discard <| withinDeadline sh.clock closeNotifyMs sh.raw.closeQuietly
        (try sh.raw.write out catch _ => pure ())
  sh.token.close
  sh.raw.closeQuietly

/-- Close with no alert (the module doc, "The close"). -/
private def Shared.abort (sh : Shared) : BaseIO Unit := do
  sh.closing.set true
  sh.token.close
  sh.raw.closeQuietly

/-- Run the handshake over `conn` in the server role when `server`
holds, and in the client role otherwise. `leftover` holds the bytes
that the negotiation read past its last message; the session takes
them before any connection byte (root §4.7). `check` decides the
peer's certificate during the handshake (the module doc, "The
certificate check"). `clock` bounds the `close_notify` write of the
secure connection.

The deadline of the handshake belongs to the caller, which closes the
connection at the expiry (root §5.4). The close wakes the read that
the handshake parks on, and the answer is `.error .closed`. -/
def handshake (ctx : Context) (server : Bool) (conn : Connection) (leftover : ByteArray)
    (check : ByteArray → Option String) (clock : Clock := Clock.system) :
    Async (Except Error Secured) := do
  let some s ← (TlsNative.sessionNew ctx.native server check : IO (Option TlsNative.Session))
    | return .error .session
  unless ← (TlsNative.feed s leftover : IO Bool) do
    return .error (.handshake (← (TlsNative.lastError s : IO String)))
  match ← handshakeLoop s conn with
  | .error e => return .error e
  | .ok () =>
    let some cert ← (TlsNative.peerCertificate s : IO (Option ByteArray))
      | return .error .noCertificate
    let alpn ← (TlsNative.alpn s : IO String)
    let token ← Chan.new 1
    discard <| (token.trySend () : BaseIO Bool)
    let sh : Shared := {
      session := s, raw := conn, token, clock
      failure := ← OnceRef.new none
      closing := ← OnceRef.new false
      tasks := ← TaskSet.new }
    return .ok {
      connection := {
        read := sh.read
        write := fun b => sh.underToken "write" (TlsNative.write s b)
        close := do
          let first ← sh.closing.updateGet fun c => (!c, true)
          if first then sh.tasks.spawn sh.closeTask
        localAddr := conn.localAddr
        remoteAddr := conn.remoteAddr }
      peerCertificate := cert
      alpn
      keyUpdate := sh.underToken "key update" (TlsNative.keyUpdate s)
      abort := sh.abort
      join := do
        sh.tasks.joinAll
        match ← (sh.failure.get : BaseIO (Option Error)) with
        | some e => return .error e
        | none => return .ok () }

end Tls
