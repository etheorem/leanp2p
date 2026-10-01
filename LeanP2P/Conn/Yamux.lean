import LeanP2P.Conn.Reader
import LeanP2P.Crypto.Bytes
import LeanP2P.Conn.Mux
import LeanP2P.Conc
import Std.Sync.Mutex
/-!
# yamux stream multiplexer (VECTOR_TEST_PLAN.md, phase 3 step 18)

Per vendor/specs/yamux/README.md (the hashicorp spec, verbatim): every
frame carries a 12-byte big-endian header

    version (8) | type (8) | flags (16) | streamID (32) | length (32)

types `Data=0 WindowUpdate=1 Ping=2 GoAway=3`, flags `SYN=1 ACK=2 FIN=4
RST=8`, client-side streams use odd ids, the session itself is id 0, Ping
and GoAway always use stream id 0. Data and WindowUpdate carry a payload /
delta in `length`; Ping carries an opaque value that is echoed back with
ACK; GoAway carries an error code (0 normal, 1 protocol, 2 internal).
Streams start with a 256 KiB receive window on both sides; `WindowUpdate`
frames return credit to the peer.

The byte codec is the verified pure core (`encode`/`decode?` with a
round-trip theorem); `YamuxSession` (below, same file) is the IO shell:
stream state machine (SYN/ACK/FIN/RST), receive-window accounting with
credit returned after the application consumes data, ping echo, and
session teardown on GoAway. The multistream-select protocol id is
`/yamux/1.0.0`.

Phase 5 (interop): the session honours the spec's flow-control rules that
the spike previously ignored - the receiver MUST acknowledge an accepted
stream (ACK on a data or window update frame), the initiator opens with
an empty SYN window update (go-yamux semantics, both sides assume the
256 KiB initial window), the sender respects the peer-granted window
(splitting writes into frames bounded by received `WindowUpdate` credit,
parking on a channel while the window is empty), and consumed data is
returned as credit in half-window batches. With these, large transfers
against go-yamux neither stall nor overflow.
-/

namespace LeanP2P.Yamux

/-! ## Big-endian helpers -/

/-- `k` big-endian bytes of `n` (most significant first). -/
def beBytes (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => n / 256 ^ k % 256 :: beBytes n k

/-- Value of big-endian bytes (inverse of `beBytes`). -/
def ofBeBytes : List Nat → Nat
  | [] => 0
  | b :: bs => b * 256 ^ bs.length + ofBeBytes bs

/-- `n % 65536` decomposed into its two bytes (linear facts for `omega`). -/
private theorem mod65536_bytes (n : Nat) :
    n % 65536 = 256 * (n / 256 % 256) + n % 256 := by
  have f1 := Nat.div_add_mod n 256
  have f2 := Nat.div_add_mod (n / 256) 256
  have e1 : n / 256 / 256 = n / 65536 := by rw [Nat.div_div_eq_div_mul]
  rw [e1] at f2
  omega

/-- `n % 4294967296` decomposed into its four bytes. -/
private theorem mod4294967296_bytes (n : Nat) :
    n % 4294967296 =
      16777216 * (n / 16777216 % 256) + 65536 * (n / 65536 % 256)
      + 256 * (n / 256 % 256) + n % 256 := by
  have f1 := Nat.div_add_mod n 256
  have f2 := Nat.div_add_mod (n / 256) 256
  have f3 := Nat.div_add_mod (n / 65536) 256
  have e1 : n / 256 / 256 = n / 65536 := by rw [Nat.div_div_eq_div_mul]
  have e2 : n / 65536 / 256 = n / 16777216 := by rw [Nat.div_div_eq_div_mul]
  rw [e1] at f2
  rw [e2] at f3
  omega

theorem ofBeBytes_be1 (n : Nat) : ofBeBytes [n % 256] = n % 256 := by
  simp [ofBeBytes]

theorem ofBeBytes_be2 (n : Nat) :
    ofBeBytes [n / 256 % 256, n % 256] = n % 65536 := by
  simp only [ofBeBytes, List.length_cons, List.length_nil, Nat.pow_zero,
    Nat.pow_one, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
  rw [mod65536_bytes]
  omega

theorem ofBeBytes_be4 (n : Nat) :
    ofBeBytes [n / 16777216 % 256, n / 65536 % 256, n / 256 % 256, n % 256]
      = n % 4294967296 := by
  simp only [ofBeBytes, List.length_cons, List.length_nil, Nat.pow_zero,
    Nat.pow_one, Nat.pow_two, Nat.mul_one, Nat.mul_zero, Nat.add_zero,
    Nat.reduceMul]
  rw [mod4294967296_bytes]
  omega

/-! ## Pure header codec -/

structure Header where
  version : Nat
  typ : Nat
  flags : Nat
  streamID : Nat
  length : Nat
  deriving Repr, BEq, DecidableEq

def tData : Nat := 0
def tWindowUpdate : Nat := 1
def tPing : Nat := 2
def tGoAway : Nat := 3

def fSYN : Nat := 1
def fACK : Nat := 2
def fFIN : Nat := 4
def fRST : Nat := 8

def version0 : Nat := 0

def initialWindow : Nat := 262144  -- 256 KiB

/-- Serialized header (12 bytes, big-endian). Fields are taken mod their
byte width, so the encoding is total; `decode_encode` fixes conformance
for well-formed headers. -/
def encode (h : Header) : List Nat :=
  [h.version % 256, h.typ % 256, h.flags / 256 % 256, h.flags % 256,
    h.streamID / 16777216 % 256, h.streamID / 65536 % 256,
    h.streamID / 256 % 256, h.streamID % 256,
    h.length / 16777216 % 256, h.length / 65536 % 256,
    h.length / 256 % 256, h.length % 256]

/-- The header carried by 12 decoded bytes. -/
def decode12 (a b c d e f g hh i j k l : Nat) : Header :=
  { version := a, typ := b, flags := 256 * c + d,
    streamID := 16777216 * e + 65536 * f + 256 * g + hh,
    length := 16777216 * i + 65536 * j + 256 * k + l }

/-- Decode a header from the front of `bs`; unconsumed bytes are returned. -/
def decode? : List Nat → Option (Header × List Nat)
  | a :: b :: c :: d :: e :: f :: g :: hh :: i :: j :: k :: l :: rest =>
      some (decode12 a b c d e f g hh i j k l, rest)
  | _ => none

/-- Decoding a serialized header recovers it and consumes exactly 12 bytes. -/
theorem decode_encode (v t fl sid ln : Nat)
    (hv : v < 256) (ht : t < 256) (hf : fl < 65536) (hs : sid < 4294967296)
    (hl : ln < 4294967296) :
    decode? (encode ⟨v, t, fl, sid, ln⟩) = some (⟨v, t, fl, sid, ln⟩, []) := by
  unfold decode? encode
  simp only [decode12, encode, List.append_assoc, List.cons_append,
    List.append_nil, ofBeBytes_be1, ofBeBytes_be2, ofBeBytes_be4,
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hf,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hl]
  have i1 : 256 * (fl / 256 % 256) + fl % 256 = fl := by
    have := mod65536_bytes fl
    have := Nat.mod_eq_of_lt hf
    omega
  have i2 : 16777216 * (sid / 16777216 % 256) + 65536 * (sid / 65536 % 256)
      + 256 * (sid / 256 % 256) + sid % 256 = sid := by
    have := mod4294967296_bytes sid
    have := Nat.mod_eq_of_lt hs
    omega
  have i3 : 16777216 * (ln / 16777216 % 256) + 65536 * (ln / 65536 % 256)
      + 256 * (ln / 256 % 256) + ln % 256 = ln := by
    have := mod4294967296_bytes ln
    have := Nat.mod_eq_of_lt hl
    omega
  rw [i1, i2, i3]

end LeanP2P.Yamux

/-! ## IO shell -/

namespace LeanP2P.Yamux

def protocol : String := "/yamux/1.0.0"

def headerToBytes (h : Header) : ByteArray :=
  Bytes.ofNatList (encode h)

/-- `be32` over an exact 4-byte slice. -/
def be32OfVal (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Read one frame: 12 header bytes then the payload. -/
def readFrame (r : BufReader) : IO (Option (Header × ByteArray)) := do
  match ← r.readExactly 12 with
  | none => pure none
  | some hb =>
    let hs := Bytes.toNatList hb
    let v0 := hs[0]!
    let v1 := hs[1]!
    let v2 := hs[2]!
    let v3 := hs[3]!
    let hdr : Header :=
      { version := v0, typ := v1, flags := 256 * v2 + v3,
        streamID := be32OfVal (hb.extract 4 8),
        length := be32OfVal (hb.extract 8 12) }
    -- only Data frames carry a payload; WindowUpdate/Ping/GoAway encode a
    -- delta / opaque value / error code in the length field
    if hdr.typ != tData then pure (some (hdr, ByteArray.empty))
    else
      match ← r.readExactly hdr.length with
      | none => pure none
      | some payload => pure (some (hdr, payload))

structure StreamState where
  pipe : Pipe
  /-- bytes received and consumed by the application, not yet returned
  as WindowUpdate credit to the peer -/
  unacked : OnceRef Nat
  /-- send credit granted by the peer's WindowUpdates (starts at the
  assumed 256 KiB initial window) -/
  sendWindow : OnceRef Nat
  /-- wakes writers parked on an empty send window -/
  credit : Chan Unit
  open_ : IO.Ref Bool
  reset : IO.Ref Bool

def StreamState.new : IO StreamState := do
  return { pipe := ← Pipe.new, unacked := ← OnceRef.new 0,
           sendWindow := ← OnceRef.new initialWindow,
           credit := ← Chan.new,
           open_ := ← IO.mkRef true, reset := ← IO.mkRef false }

structure YamuxSession where
  conn : Connection
  reader : BufReader
  streams : OnceRef (List (Nat × StreamState))
  incoming : Chan Stream
  nextId : OnceRef Nat
  dead : IO.Ref Bool
  writeMx : Std.Mutex Unit
  isClient : Bool

def YamuxSession.make (conn : Connection) (isClient : Bool) : IO YamuxSession := do
  return { conn := conn, reader := ← BufReader.ofConn conn,
           streams := ← OnceRef.new [], incoming := ← Chan.new,
           nextId := ← OnceRef.new (if isClient then 1 else 2),
           dead := ← IO.mkRef false, writeMx := ← Std.Mutex.new (),
           isClient := isClient }

def YamuxSession.writeHeader (s : YamuxSession) (h : Header) : IO Unit :=
  s.writeMx.atomically fun _ => s.conn.write (headerToBytes h)

private def YamuxSession.finStream (s : YamuxSession) (sid : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tData, flags := fFIN, streamID := sid, length := 0 })

private def YamuxSession.rstStream (s : YamuxSession) (sid : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tData, flags := fRST, streamID := sid, length := 0 })

/-- One frame per atomic write, bounded by the peer-granted send window
(yamux flow control): large writes split into credit-sized frames and the
writer parks on the stream's credit channel while the window is empty.
`credit` closes with the session, so a parked writer wakes and drops the
rest when the session dies. -/
partial def YamuxSession.writeStream (s : YamuxSession) (sid : Nat)
    (st : StreamState) (b : ByteArray) (off : Nat := 0) : IO Unit := do
  if off ≥ b.size then return
  if ← st.reset.get then return
  -- take credit atomically; `none` = window empty, park
  let taken ← st.sendWindow.update fun w =>
    let rest := b.size - off
    if w = 0 then (0, none)
    else
      let t := min w rest
      (w - t, some t)
  match taken with
  | none =>
      match ← st.credit.recv with
      | none => pure ()   -- session died: drop the rest
      | some _ => writeStream s sid st b off
  | some t => do
      let chunk := b.extract off (off + t)
      s.writeMx.atomically fun _ => do
        s.conn.write (headerToBytes { version := version0, typ := tData, flags := 0, streamID := sid, length := chunk.size })
        s.conn.write chunk
      writeStream s sid st b (off + t)

/-- Return window credit to the peer after the application consumed data. -/
def YamuxSession.windowUpdate (s : YamuxSession) (sid : Nat) (n : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tWindowUpdate, flags := 0, streamID := sid, length := n })

/-- Return consumed bytes as WindowUpdate credit to the peer, batched at
half the initial window (go-yamux sends updates the same way). -/
partial def YamuxSession.returnCredit (s : YamuxSession) (sid : Nat)
    (st : StreamState) (n : Nat) : IO Unit := do
  let tot ← st.unacked.update fun u =>
    let u' := u + n
    (u', u')
  if tot ≥ initialWindow / 2 then do
    st.unacked.set 0
    s.windowUpdate sid tot

/-- Send a ping (SYN) with an opaque value. -/
def YamuxSession.ping (s : YamuxSession) (oval : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tPing, flags := fSYN, streamID := 0, length := oval })

/-- Send GoAway (0 = normal termination). -/
def YamuxSession.goaway (s : YamuxSession) (code : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tGoAway, flags := 0, streamID := 0, length := code })

/-- The stream view handed to the application. Reads return consumed
bytes as window credit; writes honour the peer-granted send window. -/
def YamuxSession.streamOf (s : YamuxSession) (sid : Nat) (st : StreamState) : Stream where
  read := do
    match ← st.pipe.read with
    | none => pure none
    | some chunk => do
      s.returnCredit sid st chunk.size
      pure (some chunk)
  write := fun b => do
    unless b.isEmpty do
      s.writeStream sid st b
  close := s.finStream sid
  reset := s.rstStream sid

/-- Look up or create the receiving side of stream `sid`. The insertion
re-checks under the lock, so concurrent frames for a new stream id cannot
create it twice. A newly created stream is acknowledged with an empty
ACK window update (the spec requires the receiver to ACK or RST; go-yamux
acknowledges the same way). -/
def YamuxSession.getOrCreate (s : YamuxSession) (sid : Nat) :
    IO (Option StreamState) := do
  match (← s.streams.get).lookup sid with
  | some st => return (some st)
  | none =>
    if ← s.dead.get then return none
    let st' ← StreamState.new
    let (st, isNew) ← s.streams.update fun sts =>
      match sts.lookup sid with
      | some st => (sts, (st, false))
      | none => (sts ++ [(sid, st')], (st', true))
    if isNew then do
      s.writeHeader ({ version := version0, typ := tWindowUpdate, flags := fACK, streamID := sid, length := 0 })
      discard <| s.incoming.send (s.streamOf sid st)
    return (some st)

/-- Open a new stream (SYN) and return it. Ids are allocated atomically.
The SYN rides an empty window update: both sides assume the 256 KiB
initial window (go-yamux semantics; the peer grows our send window with
its own WindowUpdates). -/
def YamuxSession.openStream (s : YamuxSession) : IO (Option Stream) := do
  let sid ← s.nextId.update fun n => (n + 2, n)
  let st ← StreamState.new
  s.streams.update fun sts => (sts ++ [(sid, st)], ())
  s.writeHeader ({ version := version0, typ := tWindowUpdate, flags := fSYN, streamID := sid, length := 0 })
  return (some (s.streamOf sid st))

/-- Accept the next incoming stream (or `none` when the session dies). -/
def YamuxSession.acceptStream (s : YamuxSession) : IO (Option Stream) :=
  s.incoming.recv

/-- Session teardown: unblocks every reader, writer and the accept loop. -/
def YamuxSession.shutdown (s : YamuxSession) : IO Unit := do
  unless ← s.dead.get do
    s.dead.set true
    for (_, st) in ← s.streams.get do
      st.pipe.close
      st.credit.close
    s.incoming.close
    s.conn.close

/-- Process exactly one frame; `false` on EOF / GoAway / protocol error. -/
def YamuxSession.pumpOne (s : YamuxSession) : IO Bool := do
  match ← readFrame s.reader with
  | none => s.shutdown; pure false
  | some (hdr, payload) => do
    if hdr.version != version0 then
      s.shutdown; pure false
    else if hdr.typ == tData then
      match ← s.getOrCreate hdr.streamID with
      | none => pure false
      | some st => do
        unless payload.isEmpty do
          st.pipe.push payload
          st.unacked.update (fun u => (u + payload.size, ()))
        if hdr.flags &&& fFIN != 0 then
          st.open_.set false
          st.pipe.close
        if hdr.flags &&& fRST != 0 then
          st.reset.set true
          st.open_.set false
          st.pipe.close
          let _ ← st.credit.send ()   -- wake a parked writer so it aborts
        pure true
    else if hdr.typ == tWindowUpdate then
      -- a WindowUpdate with SYN opens a new stream; the length field is
      -- send credit for the peer (0 for the SYN/ACK control forms)
      match ← s.getOrCreate hdr.streamID with
      | none => pure false
      | some st => do
        st.sendWindow.update (fun w => (w + hdr.length, ()))
        if hdr.length > 0 then
          let _ ← st.credit.send ()
        pure true
    else if hdr.typ == tPing then
      if hdr.flags &&& fSYN != 0 then
        s.writeHeader ({ hdr with typ := tPing, flags := fACK })
      pure true
    else
      s.shutdown; pure false

/-- The frame pump: dispatch frames until EOF / GoAway / protocol error. -/
partial def YamuxSession.pump (s : YamuxSession) : IO Unit := do
  match ← s.pumpOne with
  | false => pure ()
  | true => s.pump

end LeanP2P.Yamux
