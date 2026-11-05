import Streams
import Interop.Resp

/-!
# The Redis client of the harness

The listener publishes its address with `RPUSH listenerAddr <address>`,
and the dialer takes it with `BLPOP listenerAddr <timeout>` (the
transport-interop test plan, "Dialer" step 3, "Listener" step 3). Both
first wait for the server with `PING`, as go-libp2p's test-plan peer
does (`vendor/go-libp2p/test-plans/cmd/ping/main.go`, lines 74 to 85).
This module sends those three commands over one `Streams.Connection`
and reads the replies through one `BufReader` (§4.7).

The client serves the `interop` executable alone (cli ARCHITECTURE,
contract 2), so it holds no command beyond those three.

## The bounded reads

Every read is capped before it allocates (cli ARCHITECTURE, contract
6). A reply line ends at the first CRLF, and the reader looks for it in
at most `maxReplyBytes + 2` buffered bytes. When that many bytes hold
no CRLF, the line is `tooLong`, and the reader takes no further chunk.
A bulk body is read only after its header passed `maxReplyBytes`, and
an array only after its header passed `maxArrayLength`.

`readLine` is a `partial def`: it reads until the connection supplies a
CRLF, and the connection, not an argument, bounds the loop. The cap
check before each `fill` bounds the buffer. This is the IO read loop
that CLAUDE.md names as the standing precedent for `partial`.
-/

set_option autoImplicit false

namespace Interop.Redis

open Conc (Async)
open Streams (BufReader Connection)
open Interop.Resp

/-- A reply of the three commands, after its header and its body. A
bulk string and an array carry `none` for the null forms. -/
inductive Reply where
  /-- A simple string. -/
  | simple (text : String)
  /-- An integer. -/
  | integer (value : Int)
  /-- A bulk string, or the null bulk string. -/
  | bulk (value : Option ByteArray)
  /-- An array of bulk strings, or the null array. -/
  | array (items : Option (List (Option ByteArray)))

/-- The offset of the first CRLF in the bytes, if any: the model. -/
def crlfAt? (l : List Nat) : Option Nat :=
  (l.zip l.tail).findIdx? fun (a, b) => a == cr && b == lf

/-- The offset of the first CRLF at or after `i`: the production scan,
over the `ByteArray` in place. The suite pins it to `crlfAt?`. -/
def crlfAtB? (b : ByteArray) (i : Nat := 0) : Option Nat :=
  if h : i + 1 < b.size then
    if b[i] == cr.toUInt8 && b[i + 1] == lf.toUInt8 then some i else crlfAtB? b (i + 1)
  else none
termination_by b.size - i

/-- One reply line, without its CRLF, and the reader after it. -/
partial def readLine (r : BufReader) : Async (Except Error (List Nat × BufReader)) := do
  -- `peek` copies the buffered bytes only, at most the cap and the CRLF.
  let window := r.peek (maxReplyBytes + 2)
  match crlfAtB? window with
  | some i => return .ok (Bytes.toNatList (window.extract 0 i), r.drop (i + 2))
  | none =>
    if maxReplyBytes + 2 ≤ window.size then return .error .tooLong
    -- Park: the connection read wakes it, and so does the connection's
    -- close, which ends the read with `none` (PRINCIPLES 3.1).
    match ← r.fill with
    | some r => readLine r
    | none => return .error .closed

/-- The body of a bulk string of `n` bytes, with its CRLF checked. The
caller has checked `n` against `maxReplyBytes`. -/
def readBulkBody (r : BufReader) (n : Nat) : Async (Except Error (ByteArray × BufReader)) := do
  match ← r.readExactly (n + 2) with
  | none => return .error .closed
  | some (bytes, r) =>
    if bytes.get! n == cr.toUInt8 && bytes.get! (n + 1) == lf.toUInt8 then
      return .ok (bytes.extract 0 n, r)
    else return .error (.malformed "a bulk string without its CRLF")

/-- One element of an array reply. The harness reads arrays of bulk
strings only. -/
def readBulkElement (r : BufReader) : Async (Except Error (Option ByteArray × BufReader)) := do
  match ← readLine r with
  | .error e => return .error e
  | .ok (line, r) =>
    match parseHeader line with
    | .error e => return .error e
    | .ok (.bulk none) => return .ok (none, r)
    | .ok (.bulk (some n)) =>
      match ← readBulkBody r n with
      | .error e => return .error e
      | .ok (body, r) => return .ok (some body, r)
    | .ok _ => return .error (.unexpected "an array element that is no bulk string")

/-- `k` bulk elements of an array, in order. `k` is at most
`maxArrayLength`, since the header parse checked it. -/
def readElements (r : BufReader) : Nat → Async (Except Error (List (Option ByteArray) × BufReader))
  | 0 => return .ok ([], r)
  | k + 1 => do
    match ← readBulkElement r with
    | .error e => return .error e
    | .ok (item, r) =>
      match ← readElements r k with
      | .error e => return .error e
      | .ok (items, r) => return .ok (item :: items, r)

/-- One whole reply. A simple error becomes `Error.server`. -/
def readReply (r : BufReader) : Async (Except Error (Reply × BufReader)) := do
  match ← readLine r with
  | .error e => return .error e
  | .ok (line, r) =>
    match parseHeader line with
    | .error e => return .error e
    | .ok (.simple s) => return .ok (.simple s, r)
    | .ok (.error s) => return .error (.server s)
    | .ok (.integer v) => return .ok (.integer v, r)
    | .ok (.bulk none) => return .ok (.bulk none, r)
    | .ok (.bulk (some n)) =>
      match ← readBulkBody r n with
      | .error e => return .error e
      | .ok (body, r) => return .ok (.bulk (some body), r)
    | .ok (.array none) => return .ok (.array none, r)
    | .ok (.array (some k)) =>
      match ← readElements r k with
      | .error e => return .error e
      | .ok (items, r) => return .ok (.array (some items), r)

/-! ## The client -/

/-- A client: the reader over its one connection. Each command returns
the reader after the reply, and the caller uses that one next (the
streams ARCHITECTURE, "`BufReader` is a value"). -/
structure Client where
  /-- The reader over the server connection. -/
  reader : BufReader

/-- The connection to the server. -/
def Client.conn (c : Client) : Connection := c.reader.conn

/-- Close the connection to the server. -/
def Client.close (c : Client) : IO Unit := c.conn.close

/-- A client over a connection that the caller dialed. -/
def Client.new (conn : Connection) : Client := ⟨BufReader.new conn⟩

/-- Send one command, and read its reply. -/
def Client.command (c : Client) (args : List String) : Async (Except Error (Reply × Client)) := do
  let wire := encodeCommand (args.map fun a => Bytes.toNatList (Bytes.ofString a))
  c.conn.write (Bytes.ofNatList wire)
  match ← readReply c.reader with
  | .error e => return .error e
  | .ok (reply, r) => return .ok (reply, ⟨r⟩)

/-- `PING`: the server answers `+PONG` once it serves commands. -/
def Client.ping (c : Client) : Async (Except Error Client) := do
  match ← c.command ["PING"] with
  | .error e => return .error e
  | .ok (.simple "PONG", c) => return .ok c
  | .ok _ => return .error (.unexpected "a PING answer other than PONG")

/-- `RPUSH key value`: the server answers the new length of the list. -/
def Client.rpush (c : Client) (key value : String) : Async (Except Error Client) := do
  match ← c.command ["RPUSH", key, value] with
  | .error e => return .error e
  | .ok (.integer _, c) => return .ok c
  | .ok _ => return .error (.unexpected "an RPUSH answer that is no integer")

/-- `BLPOP key timeout`: the value at the head of the list, or `none`
when `timeoutSec` seconds pass first. The server answers the key and
the value as a two-element array, or the null array at the timeout. -/
def Client.blpop (c : Client) (key : String) (timeoutSec : Nat) :
    Async (Except Error (Option String × Client)) := do
  match ← c.command ["BLPOP", key, toString timeoutSec] with
  | .error e => return .error e
  | .ok (.array none, c) => return .ok (none, c)
  | .ok (.array (some [some _, some value]), c) =>
    match Bytes.toString? value with
    | some text => return .ok (some text, c)
    | none => return .error (.malformed "a BLPOP value that is not UTF-8")
  | .ok _ => return .error (.unexpected "a BLPOP answer that is no key and value")

end Interop.Redis
