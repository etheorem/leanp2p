import LeanP2P.Net.Tcp
import LeanP2P.Conn.Reader
import LeanP2P.Crypto.Bytes
import LeanP2P.Crypto.OpenSsl
/-!
# Minimal Redis client (VECTOR_TEST_PLAN.md, phase 5 step 25)

The transport-interop harness coordinates dialer and listener through two
Redis commands: the listener `RPUSH`es its multiaddr onto the
`listenerAddr` list, the dialer `BLPOP`s it. This is a RESP2 client over
the Lean TCP transport with just that surface (plus `DEL` / `PING` for
the harness scripts): command arrays of bulk strings, inline replies
parsed per the RESP2 reply map. Only `ip:port` server addresses are
accepted (the harness scripts pass container IPs; no DNS in the spike).
-/

namespace LeanP2P.Interop.Redis

/-- A connected Redis client: the raw connection plus a buffered reader. -/
structure Client where
  conn : Connection
  reader : BufReader

def parseIp4? (h : String) : Option (Nat × Nat × Nat × Nat) := do
  match h.splitOn "." with
  | [a, b, c, d] =>
    let x := a.toNat?; let y := b.toNat?
    let z := c.toNat?; let w := d.toNat?
    match x, y, z, w with
    | some x, some y, some z, some w =>
        if x < 256 ∧ y < 256 ∧ z < 256 ∧ w < 256 then some (x, y, z, w) else none
    | _, _, _, _ => none
  | _ => none

/-- `host:port` to a `/ip4/../tcp/..` multiaddr. The host may be a dotted
ip4, `localhost`, or any DNS name (resolved through the shim's
getaddrinfo - the test-plans runner passes the compose service name
`redis`). -/
def addrOfHostPort? (hostPort : String) : IO (Option Multiaddr) := do
  match hostPort.splitOn ":" with
  | [h, p] =>
    let some port := p.toNat? | pure none
    if port ≥ 65536 then pure none
    else do
      let ip? ←
        if h == "localhost" then pure (some (127, 0, 0, 1))
        else match parseIp4? h with
          | some q => pure (some q)
          | none => do
            match ← OpenSsl.resolveV4 h with
            | some b4 => pure (parseIp4? s!"{b4[0]!.toNat}.{b4[1]!.toNat}.{b4[2]!.toNat}.{b4[3]!.toNat}")
            | none => pure none
      match ip? with
      | some (a, b, c, d) =>
          pure (some { components := [AddrComponent.ip4 a b c d, AddrComponent.tcp port] })
      | none => pure none
  | _ => pure none

/-- Connect to `host:port` (DNS names resolved; `none` on failure). -/
def connect? (hostPort : String) : IO (Option Client) := do
  let some addr ← addrOfHostPort? hostPort | return none
  let some c ← Tcp.dial addr | return none
  return some { conn := c, reader := ← BufReader.ofConn c }

def Client.close (r : Client) : IO Unit :=
  r.conn.close

/-! ## RESP2 wire forms -/

/-- One RESP2 reply. -/
inductive Reply where
  | status (s : String)        -- `+OK`
  | error (s : String)         -- `-ERR ...`
  | int (n : Int)              -- `:1`
  | bulk (b : Option ByteArray)-- `$6\r\nfoobar` / `$-1` (nil)
  | array (xs : List Reply)    -- `*2 ...`

/-- Serialize a command (array of bulk strings). -/
def encodeCmd (args : List String) : ByteArray :=
  let head := Bytes.ofString s!"*{args.length}\r\n"
  args.foldl (fun acc a =>
    acc ++ Bytes.ofString s!"${(a.toUTF8).size}\r\n" ++ a.toUTF8 ++ Bytes.ofString "\r\n") head

/-- One CRLF-terminated line off the reader (the over-read stays buffered
for the next reply). The buffer is drained up front: bytes taken into
`acc` must not be served again by `readAvail` (the same fault the phase 5
`readExactly` fix removed - a lone `\r` split across TCP reads used to
duplicate the buffered prefix and desync the reply stream). -/
partial def readLine (r : BufReader) : IO (Option String) := do
  let first ← r.buf.get
  r.buf.set ByteArray.empty
  let rec go (acc : ByteArray) : IO (Option String) := do
    match acc.toList.findIdx? (· == 13) with
    | some i =>
      if acc.size > i + 1 then do
        r.buf.set (acc.extract (i + 2) acc.size)
        pure (Bytes.toString? (acc.extract 0 i))
      else
        match ← r.readAvail with
        | none => pure none
        | some c => go (acc ++ c)
    | none =>
      match ← r.readAvail with
      | none => pure none
      | some c => go (acc ++ c)
  go first

/-- Read one reply (recursively for arrays). -/
partial def reply (r : BufReader) : IO (Option Reply) := do
  match ← readLine r with
  | none => pure none
  | some l =>
    match l.get? 0 with
    | some '+' => pure (Reply.status (l.drop 1).toString)
    | some '-' => pure (Reply.error (l.drop 1).toString)
    | some ':' =>
        match (l.drop 1).toInt? with
        | some n => pure (Reply.int n)
        | none => pure none
    | some '$' =>
        match (l.drop 1).toInt? with
        | some (-1) => pure (Reply.bulk none)
        | some n =>
          if n < -1 then pure none
          else match ← r.readExactly n.toNat with
          | none => pure none
          | some b => do
            let _ ← readLine r   -- trailing CRLF
            pure (Reply.bulk (some b))
        | none => pure none
    | some '*' =>
        match (l.drop 1).toNat? with
        | some n => do
          let rec go : Nat → List Reply → IO (Option (List Reply))
            | 0, acc => pure (some acc.reverse)
            | k + 1, acc => do
              match ← reply r with
              | none => pure none
              | some x => go k (x :: acc)
          let xs? ← go n []
          pure (Reply.array <$> xs?)
        | none => pure none
    | _ => pure none

/-- Run one command; `none` on connection failure. -/
def cmd (r : Client) (args : List String) : IO (Option Reply) := do
  r.conn.write (encodeCmd args)
  reply r.reader

/-- `RPUSH key val` → list length. -/
def rpush (r : Client) (key val : String) : IO (Option Int) := do
  match ← cmd r ["RPUSH", key, val] with
  | some (Reply.int n) => pure (some n)
  | _ => pure none

/-- `BLPOP key timeout` → the popped value, or `none` on timeout / error.
`timeoutSecs = 0` blocks forever (avoid: pass the test timeout). -/
def blpop (r : Client) (key : String) (timeoutSecs : Nat) :
    IO (Option String) := do
  match ← cmd r ["BLPOP", key, toString timeoutSecs] with
  | some (Reply.array [_, Reply.bulk (some v)]) => pure (Bytes.toString? v)
  | _ => pure none

/-- `DEL key`. -/
def del (r : Client) (key : String) : IO Bool := do
  match ← cmd r ["DEL", key] with
  | some (Reply.int _) => pure true
  | _ => pure false

end LeanP2P.Interop.Redis
