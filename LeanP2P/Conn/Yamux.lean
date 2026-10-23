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

/-- Largest Data-frame payload accepted off the wire: a compliant peer
never sends more than the 256 KiB receive window we start every stream
with (and only grows it with our WindowUpdates), so anything larger is a
protocol violation, not a frame to allocate. Bounds the receive path:
the length field is a 32-bit value and would otherwise commit us to
reading up to 4 GiB into memory. -/
def maxDataFrame : Nat := initialWindow

/-- The control queue is capped: a hostile ping/ACK flood must not grow
it without bound (each queued header is small, but the queue itself is
unbounded otherwise). Beyond the cap, control frames are dropped - they
are all either acknowledgements (a lost ACK costs one retransmit-free
retransmission on the peer's side: it re-sends, we re-ACK) or ping
echoes (a lost echo times out on the pinger). -/
def maxControlQ : Nat := 1024

def headerToBytes (h : Header) : ByteArray :=
  Bytes.ofNatList (encode h)

/-- `be32` over an exact 4-byte slice. -/
def be32OfVal (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Read one frame: 12 header bytes then the payload. A Data frame whose
declared length exceeds `maxDataFrame` is a protocol error (`none` ->
the pump shuts the session down). -/
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
    else if hdr.length > maxDataFrame then pure none
    else
      match ← r.readExactly hdr.length with
      | none => pure none
      | some payload => pure (some (hdr, payload))

structure StreamState where
  pipe : Pipe
  /-- bytes consumed by the application, not yet returned as
  WindowUpdate credit to the peer -/
  unacked : OnceRef Nat
  /-- send credit granted by the peer's WindowUpdates (starts at the
  assumed 256 KiB initial window) -/
  sendWindow : OnceRef Nat
  /-- receive window we have granted the peer (starts at the initial
  window, shrinks with inbound data, grows back when credit is returned);
  inbound data beyond it is a flow-control violation -/
  recvWindow : OnceRef Nat
  /-- wakes writers parked on an empty send window -/
  credit : Chan Unit
  /-- writers currently parked on `credit` - wake tokens are sent only
  when this is positive, so no tokens accumulate while nobody waits -/
  parked : OnceRef Nat
  /-- our write side has sent FIN (half-close: reads keep working) -/
  sentFin : IO.Ref Bool
  reset : IO.Ref Bool

def StreamState.new : IO StreamState := do
  return { pipe := ← Pipe.new, unacked := ← OnceRef.new 0,
           sendWindow := ← OnceRef.new initialWindow,
           recvWindow := ← OnceRef.new initialWindow,
           credit := ← Chan.new,
           parked := ← OnceRef.new 0,
           sentFin := ← IO.mkRef false, reset := ← IO.mkRef false }

structure YamuxSession where
  conn : Connection
  reader : BufReader
  streams : OnceRef (List (Nat × StreamState))
  incoming : Chan Stream
  nextId : OnceRef Nat
  dead : OnceRef Bool
  writeMx : Std.Mutex Unit
  /-- control frames generated by the frame pump (new-stream ACKs, ping
  echoes) are queued here instead of written inline: the pump must never
  block on `writeMx`, or a stream writer parked in `conn.write` on a full
  TCP buffer could deadlock both sessions' pumps at once. Capped at
  `maxControlQ` (see above). -/
  controlQ : Chan Header
  controlDepth : OnceRef Nat
  isClient : Bool

def YamuxSession.make (r : BufReader) (isClient : Bool) : IO YamuxSession := do
  return { conn := r.conn, reader := r,
           streams := ← OnceRef.new [], incoming := ← Chan.new,
           nextId := ← OnceRef.new (if isClient then 1 else 2),
           dead := ← OnceRef.new false, writeMx := ← Std.Mutex.new (),
           controlQ := ← Chan.new, controlDepth := ← OnceRef.new 0,
           isClient := isClient }

def YamuxSession.writeHeader (s : YamuxSession) (h : Header) : IO Unit :=
  s.writeMx.atomically fun _ => s.conn.write (headerToBytes h)

/-- Queue a control frame, unless the cap is hit (`false` = dropped).
The depth counter and the send are one atomic step against the pump's
decrement, so the cap cannot be overshot by concurrent producers. -/
def YamuxSession.queueControl (s : YamuxSession) (h : Header) : IO Bool := do
  let queued ← s.controlDepth.update fun d =>
    if d < maxControlQ then (d + 1, true) else (d, false)
  if queued then discard <| s.controlQ.send h
  pure queued

/-- Write exactly one queued control frame (`false` when the session shut
down). The deterministic suites drive this by hand; the IO shell runs
`controlLoop`. -/
def YamuxSession.controlOne (s : YamuxSession) : IO Bool := do
  match ← s.controlQ.recv with
  | none => pure false
  | some h => do
    s.controlDepth.update fun d => (d - 1, ())
    s.writeHeader h
    pure true

/-- Drain the control queue, writing each frame under the write mutex.
Runs as its own task; exits when the session shuts down (queue closed). -/
partial def YamuxSession.controlLoop (s : YamuxSession) : IO Unit := do
  match ← s.controlOne with
  | false => pure ()
  | true => controlLoop s

private def YamuxSession.finStream (s : YamuxSession) (sid : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tData, flags := fFIN, streamID := sid, length := 0 })

private def YamuxSession.rstStream (s : YamuxSession) (sid : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tData, flags := fRST, streamID := sid, length := 0 })

/-- Forget a stream (both directions are done with it): taken out of the
session map, writers locked out, pipes and credit closed. Without this
the session list only grows over a long-lived connection and every
lookup walks it linearly. -/
def YamuxSession.removeStream (s : YamuxSession) (sid : Nat) : IO Unit := do
  let removed? ← s.streams.update fun sts =>
    match sts.lookup sid with
    | none => (sts, none)
    | some st => (sts.filter (fun x => x.1 != sid), some st)
  match removed? with
  | none => pure ()
  | some st => do
    st.reset.set true
    st.pipe.close
    st.credit.close

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
      -- park (counted, so wake sources can tell whether anyone waits).
      -- The re-check closes the race with a concurrent WindowUpdate:
      -- if credit arrives between the `taken = none` read and the park,
      -- the second window read sees it and we simply retry.
      st.parked.update fun n => (n + 1, ())
      let woke ←
        if (← st.sendWindow.get) > 0 then
          st.parked.update fun n => (n - 1, ())
          pure (some ())
        else do
          let w ←
            try
              st.credit.recv
            finally
              st.parked.update fun n => (n - 1, ())
          pure w
      match woke with
      | none => pure ()   -- session died / stream reset: drop the rest
      | some _ => writeStream s sid st b off
  | some t => do
      let chunk := b.extract off (off + t)
      s.writeMx.atomically fun _ => do
        s.conn.write (headerToBytes { version := version0, typ := tData, flags := 0, streamID := sid, length := chunk.size })
        s.conn.write chunk
      -- hand the wake on: when credit remains but other writers of this
      -- stream are parked, a WindowUpdate woke only *us* - without this
      -- the second writer sleeps until the peer happens to grant more
      if (← st.sendWindow.get) > 0 ∧ (← st.parked.get) > 0 then
        let _ ← st.credit.send ()
      writeStream s sid st b (off + t)

/-- Return window credit to the peer after the application consumed data. -/
def YamuxSession.windowUpdate (s : YamuxSession) (sid : Nat) (n : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tWindowUpdate, flags := 0, streamID := sid, length := n })

/-- Return consumed bytes as WindowUpdate credit to the peer, batched at
half the initial window (go-yamux sends updates the same way). The
accumulation and the flush are one atomic step, so concurrent readers of
the stream cannot lose credit. The receive window is replenished here:
from this point the peer may send the returned bytes again, so inbound
data is bounded by the window we have actually granted. -/
def YamuxSession.returnCredit (s : YamuxSession) (sid : Nat)
    (st : StreamState) (n : Nat) : IO Unit := do
  st.recvWindow.update fun w => (w + n, ())
  let send? ← st.unacked.update fun u =>
    let u' := u + n
    if u' ≥ initialWindow / 2 then (0, some u') else (u', none)
  match send? with
  | some tot => s.windowUpdate sid tot
  | none => pure ()

/-- Send a ping (SYN) with an opaque value. -/
def YamuxSession.ping (s : YamuxSession) (oval : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tPing, flags := fSYN, streamID := 0, length := oval })

/-- Send GoAway (0 = normal termination). -/
def YamuxSession.goaway (s : YamuxSession) (code : Nat) : IO Unit :=
  s.writeHeader ({ version := version0, typ := tGoAway, flags := 0, streamID := 0, length := code })

/-- The stream view handed to the application. Reads return consumed
bytes as window credit; writes honour the peer-granted send window.
`close` is a half-close: it ends our write direction only, so a response
the peer sends after our FIN still arrives (yamux FIN = "no more data
from this sender"). -/
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
  close := do
    unless ← st.sentFin.get do
      st.sentFin.set true
      s.finStream sid
      -- the peer had already closed our read side: the stream is fully
      -- done on both directions, retire it
      if ← st.pipe.ch.closed.get then
        s.removeStream sid
  reset := s.rstStream sid

/-- Look up an established stream (no creation). -/
def YamuxSession.getStream (s : YamuxSession) (sid : Nat) :
    IO (Option StreamState) := do
  pure ((← s.streams.get).lookup sid)

/-- Accept a remote-initiated stream (a SYN-carrying frame): the id must
have the remote's parity (our ids are odd for the client, even for the
server - a frame with our parity collides with a future `openStream` and
is rejected), insertion re-checks under the lock so concurrent frames for
a new stream id cannot create it twice, and a newly created stream is
acknowledged with an empty ACK window update (the spec requires the
receiver to ACK or RST; go-yamux acknowledges the same way). Data and
WindowUpdate frames *without* SYN never create streams - they are
dropped by the pump instead of inventing state. -/
def YamuxSession.acceptRemote (s : YamuxSession) (sid : Nat) :
    IO (Option StreamState) := do
  -- remote-initiated ids have the parity opposite to ours
  let parityOk := if s.isClient then sid % 2 == 0 else sid % 2 == 1
  if !parityOk then return none
  match (← s.streams.get).lookup sid with
  | some st => return (some st)
  | none =>
    if ← s.dead.get then return none
    let st' ← StreamState.new
    let (st, isNew) ← s.streams.update fun sts =>
      match sts.lookup sid with
      | some st => (sts, (st, false))
      | none => (sts ++ [(sid, st')], (st', true))
    -- inserted after shutdown ran? retire the candidate ourselves
    if ← s.dead.get then do
      if isNew then
        st'.pipe.close
        st'.credit.close
      return none
    if isNew then do
      let _ ← s.queueControl { version := version0, typ := tWindowUpdate, flags := fACK, streamID := sid, length := 0 }
      discard <| s.incoming.send (s.streamOf sid st)
    return (some st)

/-- Open a new stream (SYN) and return it. Ids are allocated atomically.
The SYN rides an empty window update: both sides assume the 256 KiB
initial window (go-yamux semantics; the peer grows our send window with
its own WindowUpdates). `none` once the session is dead (a stream opened
on a dead session would park forever). -/
def YamuxSession.openStream (s : YamuxSession) : IO (Option Stream) := do
  if ← s.dead.get then return none
  let sid ← s.nextId.update fun n => (n + 2, n)
  let st ← StreamState.new
  s.streams.update fun sts => (sts ++ [(sid, st)], ())
  -- the session may have died while we inserted: retire the new stream
  -- ourselves (shutdown only sweeps streams registered before it ran)
  if ← s.dead.get then do
    st.pipe.close
    st.credit.close
    return none
  s.writeHeader ({ version := version0, typ := tWindowUpdate, flags := fSYN, streamID := sid, length := 0 })
  return (some (s.streamOf sid st))

/-- Accept the next incoming stream (or `none` when the session dies). -/
def YamuxSession.acceptStream (s : YamuxSession) : IO (Option Stream) :=
  s.incoming.recv

/-- Session teardown: unblocks every reader, writer and the accept loop.
Test-and-set on the dead flag, so exactly one caller runs the sweep
(streams created afterwards retire themselves - see `openStream` and
`acceptRemote`). -/
def YamuxSession.shutdown (s : YamuxSession) : IO Unit := do
  let wasDead ← s.dead.update fun d => (true, d)
  unless wasDead do
    for (_, st) in ← s.streams.get do
      st.pipe.close
      st.credit.close
    s.incoming.close
    s.controlQ.close
    s.conn.close

/-- Process exactly one frame; `false` on EOF / GoAway / protocol error.
Frames for streams that do not exist are dropped (no state is invented:
only a SYN creates a stream, with the remote's parity). Inbound Data
beyond the receive window we granted is a flow-control violation and
shuts the session down, like go-yamux. -/
def YamuxSession.pumpOne (s : YamuxSession) : IO Bool := do
  match ← readFrame s.reader with
  | none => s.shutdown; pure false
  | some (hdr, payload) => do
    if hdr.version != version0 then
      s.shutdown; pure false
    else if hdr.typ == tData then
      match ← s.getStream hdr.streamID with
      | none => pure true   -- unknown stream, no SYN: drop the frame
      | some st => do
        -- enforce the receive window we granted the peer
        let ok ← st.recvWindow.update fun w =>
          if payload.size ≤ w then (w - payload.size, true) else (w, false)
        if !ok then do s.shutdown; pure false
        else do
          unless payload.isEmpty do
            st.pipe.push payload
          if hdr.flags &&& fFIN != 0 then
            -- half-close: EOF for our readers; our writes keep working.
            -- When we have also sent FIN, the stream is done both ways.
            st.pipe.close
            if ← st.sentFin.get then s.removeStream hdr.streamID
          if hdr.flags &&& fRST != 0 then
            st.reset.set true
            -- close (not send): wakes *every* parked writer, and writers
            -- that park later see the closed channel immediately
            st.pipe.close
            st.credit.close
            s.removeStream hdr.streamID
          pure true
    else if hdr.typ == tWindowUpdate then
      -- a WindowUpdate with SYN opens a new stream; the length field is
      -- send credit for the peer (0 for the SYN/ACK control forms)
      let st? ←
        if hdr.flags &&& fSYN != 0 then s.acceptRemote hdr.streamID
        else s.getStream hdr.streamID
      match st? with
      | none => pure true   -- unknown stream, no SYN: drop
      | some st => do
        st.sendWindow.update (fun w => (w + hdr.length, ()))
        -- wake a parked writer only (no tokens pile up otherwise)
        if hdr.length > 0 ∧ (← st.parked.get) > 0 then
          let _ ← st.credit.send ()
        pure true
    else if hdr.typ == tPing then
      if hdr.flags &&& fSYN != 0 then
        let _ ← s.queueControl { hdr with typ := tPing, flags := fACK }
      pure true
    else
      s.shutdown; pure false

/-- The frame pump: dispatch frames until EOF / GoAway / protocol error. -/
partial def YamuxSession.pump (s : YamuxSession) : IO Unit := do
  match ← s.pumpOne with
  | false => pure ()
  | true => s.pump

end LeanP2P.Yamux
