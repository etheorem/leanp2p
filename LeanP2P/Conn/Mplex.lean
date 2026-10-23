import LeanP2P.Conn.Reader
import LeanP2P.Crypto.Bytes
import LeanP2P.Conn.Mux
import LeanP2P.Conn.Stream
import LeanP2P.Conc
import Std.Sync.Mutex
/-!
# mplex stream multiplexer (VECTOR_TEST_PLAN.md, phase 3 step 19)

Per vendor/specs/mplex/README.md: every message is

    | header (uvarint) | length (uvarint) | data ('length' bytes) |

The header's lower three bits are the message flag and the remaining bits
are the stream id (`header = (id << 3) | flag`). Flags: NewStream 0,
MessageReceiver 1, MessageInitiator 2, CloseReceiver 3, CloseInitiator 4,
ResetReceiver 5, ResetInitiator 6 - the Receiver/Initiator suffix is
relative to the stream initiator. New streams open with a NewStream
message whose data is the stream name; payloads are capped at 1 MiB.

Phase 5 (interop): stream identity follows go-mplex exactly. Both sides
number their locally-initiated streams from zero, so an id alone does not
name a stream - the Receiver/Initiator flag does ("Both parties can open
a substream with the same ID, therefore this distinction is used to
identify whether each message concerns the channel opened locally or
remotely"). Streams are therefore keyed by `(id, weInitiated)` and every
inbound flag routes to the key the flag names: `MessageReceiver` /
`CloseReceiver` / `ResetReceiver` concern the stream the *local* side
initiated, `NewStream` / `MessageInitiator` / `CloseInitiator` /
`ResetInitiator` the stream the *remote* side initiated.

The byte codec is the verified pure core (`encodeMsg`/`decodeMsg?` with a
round-trip theorem); `MplexSession` is the IO shell with per-direction
message routing. The multistream-select protocol id is `/mplex/6.7.0`.
-/

namespace LeanP2P.Mplex

def protocol : String := "/mplex/6.7.0"

/-- 1 MiB per message. -/
def maxMsg : Nat := 1048576

def fNewStream : Nat := 0
def fMessageReceiver : Nat := 1
def fMessageInitiator : Nat := 2
def fCloseReceiver : Nat := 3
def fCloseInitiator : Nat := 4
def fResetReceiver : Nat := 5
def fResetInitiator : Nat := 6

/-- Header varint: `(id << 3) | flag`. -/
def headerVal (flag id : Nat) : Nat := id * 8 + flag

/-- One message: flag, stream id, payload (the `List Nat` byte model). -/
structure Msg where
  flag : Nat
  id : Nat
  payload : List Nat
  deriving Repr, BEq

/-- Serialized message: header varint, payload-length varint, payload. -/
def encodeMsg (m : Msg) : List Nat :=
  Varint.encode (headerVal m.flag m.id) ++
  Varint.encode m.payload.length ++
  m.payload

/-- Decode outcome: need more bytes, protocol error, or a message plus the
unconsumed rest. -/
inductive MsgDecode where
  | more (need : Nat)
  | bad
  | done (msg : Msg) (consumed : Nat)

/-- Decode one message; `consumed` counts every byte taken off `bs`. A
varint that cannot complete within the 9-byte uvarint limit is a protocol
error, not "need more bytes" - otherwise the reader accumulates forever
on a hostile header (the 9-byte bound is `Varint.decode?`'s own). -/
def decodeMsg? : List Nat → MsgDecode
  | bs =>
    match Varint.decode? bs with
    | none => if bs.length ≥ 9 then .bad else .more 1
    | some (key, rest) =>
      if key % 8 > 6 then .bad
      else
        match Varint.decode? rest with
        | none => if rest.length ≥ 9 then .bad else .more (bs.length + 1)
        | some (len, rest2) =>
          if len > maxMsg then .bad
          else if rest2.length < len then .more (bs.length + (len - rest2.length))
          else
            .done { flag := key % 8, id := key / 8, payload := rest2.take len }
              (bs.length - rest2.length + len)

/-- Decoding a serialized message recovers it and consumes everything. -/
theorem decode_encode (m : Msg)
    (hf : m.flag ≤ 6) (hid : m.id < 2 ^ 60) (hp : m.payload.length ≤ maxMsg) :
    decodeMsg? (encodeMsg m) = .done m (encodeMsg m).length := by
  have h63 : headerVal m.flag m.id < 2 ^ 63 := by
    unfold headerVal
    have h2 : m.id < 2 ^ 60 := hid
    have h3 : (2 : Nat) ^ 63 = 8 * 2 ^ 60 := by decide
    omega
  have hlen : (Varint.encode (headerVal m.flag m.id)).length ≤ 9 := by
    unfold headerVal
    exact Varint.encode_length_le _ h63
  have hplen : m.payload.length < 2 ^ 63 := by
    have := hp
    simp only [maxMsg] at this
    omega
  have hlen2 : (Varint.encode m.payload.length).length ≤ 9 :=
    Varint.encode_length_le _ hplen
  have hflag : headerVal m.flag m.id % 8 = m.flag := by
    unfold headerVal
    have h1 := Nat.div_add_mod m.id 8
    have h2 : m.id / 8 * 8 = 8 * (m.id / 8) := Nat.mul_comm _ _
    omega
  have hid8 : headerVal m.flag m.id / 8 = m.id := by
    unfold headerVal
    omega
  unfold decodeMsg?
  simp only [encodeMsg, Varint.decode?, List.append_assoc,
    Varint.decodeF_encode_app (headerVal m.flag m.id)
      (Varint.encode m.payload.length ++ m.payload) h63 9 hlen,
    Varint.decodeF_encode_app m.payload.length m.payload hplen 9 hlen2,
    hflag, hid8]
  have hplen3 : m.payload.length ≤ (Varint.encode (headerVal m.flag m.id) ++
      (Varint.encode m.payload.length ++ m.payload)).length := by
    have h6 : (Varint.encode (headerVal m.flag m.id) ++
        (Varint.encode m.payload.length ++ m.payload)).length
        = (Varint.encode (headerVal m.flag m.id)).length
          + (Varint.encode m.payload.length ++ m.payload).length := by
      simp [List.length_append]
    have h7 : (Varint.encode m.payload.length ++ m.payload).length
        = (Varint.encode m.payload.length).length + m.payload.length := by
      simp [List.length_append]
    omega
  split
  · exact absurd hf (by omega)
  split
  · exact absurd hp (by omega)
  split
  · exact absurd (Nat.lt_irrefl m.payload.length) (by omega)
  · congr 2
    · simp [List.take_length]
    · omega

structure MplexStream where
  id : Nat
  pipe : Pipe
  initiator : Bool
  /-- our write direction is open (a remote Close does NOT close it:
  half-close semantics - close ends the closer's writing only) -/
  writeOpen : IO.Ref Bool

structure MplexSession where
  conn : Connection
  reader : BufReader
  /-- streams keyed by `(id, weInitiated)` - both sides number their own
  streams from zero, the flag bit disambiguates (go-mplex identity) -/
  streams : OnceRef (List ((Nat × Bool) × MplexStream))
  incoming : Chan Stream
  nextId : OnceRef Nat
  dead : IO.Ref Bool
  writeMx : Std.Mutex Unit
  isClient : Bool

def MplexSession.make (r : BufReader) (isClient : Bool) : IO MplexSession := do
  return { conn := r.conn, reader := r,
           streams := ← OnceRef.new [], incoming := ← Chan.new,
           nextId := ← OnceRef.new 0,
           dead := ← IO.mkRef false, writeMx := ← Std.Mutex.new (),
           isClient := isClient }

def MplexSession.writeMsg (s : MplexSession) (m : Msg) : IO Unit :=
  s.writeMx.atomically fun _ => s.conn.write (Bytes.ofNatList (encodeMsg m))

/-- Forget a stream (both directions are done): out of the session map,
so a long-lived connection does not accumulate entries and every lookup
stays cheap. -/
def MplexSession.removeStream (s : MplexSession) (key : Nat × Bool) : IO Unit :=
  s.streams.update fun sts => (sts.filter (fun x => x.1 != key), ())

/-- The stream view handed to the application. Half-close per the spec:
"Closing a stream closes it for writing and closes the remote end for
reading but allows writing in the other direction" - local `close` ends
our writes only; reads keep returning data until the peer closes. -/
def MplexSession.streamOf (s : MplexSession) (st : MplexStream) : Stream where
  read := st.pipe.read
  write := fun b => do
    if ← st.writeOpen.get then
      let flag := if st.initiator then fMessageInitiator else fMessageReceiver
      s.writeMsg { flag := flag, id := st.id, payload := Bytes.toNatList b }
  close := do
    if ← st.writeOpen.get then
      let flag := if st.initiator then fCloseInitiator else fCloseReceiver
      s.writeMsg { flag := flag, id := st.id, payload := [] }
      st.writeOpen.set false
      -- the peer already closed (our reads are at EOF): the stream is
      -- fully done on both directions, retire it
      if ← st.pipe.ch.closed.get then
        s.removeStream (st.id, st.initiator)
    -- reads stay open: the peer may still be sending (half-close)
  reset := do
    -- reset is abortive in both directions; send it once
    if ← st.writeOpen.get then
      let flag := if st.initiator then fResetInitiator else fResetReceiver
      s.writeMsg { flag := flag, id := st.id, payload := [] }
      st.writeOpen.set false
    st.pipe.close

/-- Open a new stream (NewStream carrying the stream name). Ids are
allocated atomically and counted from zero on both sides (go-mplex). -/
def MplexSession.openStream (s : MplexSession) (protocolName : String) :
    IO (Option Stream) := do
  let sid ← s.nextId.update fun n => (n + 1, n)
  let st : MplexStream :=
    { id := sid, pipe := ← Pipe.new, initiator := true, writeOpen := ← IO.mkRef true }
  s.streams.update fun sts => (sts ++ [((sid, true), st)], ())
  s.writeMsg { flag := fNewStream, id := sid,
               payload := Bytes.toNatList (Bytes.ofString protocolName) }
  return (some (s.streamOf st))

/-- Accept the next incoming stream. -/
def MplexSession.acceptStream (s : MplexSession) : IO (Option Stream) :=
  s.incoming.recv

/-- Look up or create the receiving side of stream `id` (insertion
re-checks under the lock). `locallyInitiated` selects the namespace: only
`NewStream` creates a remote-initiated stream; messages for streams that
do not exist are dropped (go-mplex logs and ignores them). -/
def MplexSession.getOrCreate (s : MplexSession) (id : Nat)
    (locallyInitiated : Bool) : IO (Option MplexStream) := do
  match (← s.streams.get).lookup (id, locallyInitiated) with
  | some st => return (some st)
  | none =>
    if ← s.dead.get then return none
    let st' : MplexStream :=
      { id := id, pipe := ← Pipe.new, initiator := locallyInitiated, writeOpen := ← IO.mkRef true }
    let (st, isNew) ← s.streams.update fun sts =>
      match sts.lookup (id, locallyInitiated) with
      | some st => (sts, (st, false))
      | none => (sts ++ [((id, locallyInitiated), st')], (st', true))
    if isNew then discard <| s.incoming.send (s.streamOf st)
    return (some st)

/-- Read one mplex message through the buffered reader. -/
partial def readFrame (r : BufReader) : IO (Option Msg) := do
  -- header uvarint (≤ 9 bytes), then the payload-length uvarint, then data
  let rec go (acc : List Nat) : IO (Option Msg) := do
    match decodeMsg? acc with
    | .bad => return none
    | .done m c => do
      r.buf.set (Bytes.ofNatList (acc.drop c))
      return (some m)
    | .more _ => do
      match ← r.readAvail with
      | none => return none
      | some chunk => go (acc ++ Bytes.toNatList chunk)
  go []

/-- Session teardown: unblocks every reader and the accept loop. -/
def MplexSession.shutdown (s : MplexSession) : IO Unit := do
  unless ← s.dead.get do
    s.dead.set true
    for (_, st) in ← s.streams.get do
      st.pipe.close
    s.incoming.close
    s.conn.close

/-- Route one inbound message to the stream the flag names. The
Receiver/Initiator suffix is relative to the *stream* initiator: a
`*Receiver` flag concerns the stream the local side initiated,
`NewStream` and the `*Initiator` flags the stream the remote side
initiated (go-mplex identity; see the module doc).

Close/Reset follow the spec's half-close rule: a peer Close ends *its*
write direction - our reads drain to EOF, our writes keep working (the
local `writeOpen` flag is untouched). A Reset kills both directions and
retires the stream. Messages for streams that do not exist are dropped
(go-mplex logs and ignores them). -/
def MplexSession.pumpOne (s : MplexSession) : IO Bool := do
  match ← readFrame s.reader with
  | none => s.shutdown; pure false
  | some msg => do
    if msg.flag == fNewStream then do
      -- NewStream carries the stream name (for debugging only), not data
      match ← s.getOrCreate msg.id false with
      | none => pure false
      | some _ => pure true
    else if msg.flag == fMessageReceiver then do
      -- data from the stream's receiver: one of our locally-initiated
      -- streams; unknown ids are dropped, like go-mplex
      match (← s.streams.get).lookup (msg.id, true) with
      | some st => do st.pipe.push (Bytes.ofNatList msg.payload); pure true
      | none => pure true
    else if msg.flag == fMessageInitiator then do
      -- data from the stream's initiator: a remote-initiated stream
      match (← s.streams.get).lookup (msg.id, false) with
      | some st => do st.pipe.push (Bytes.ofNatList msg.payload); pure true
      | none => pure true
    else if msg.flag == fCloseReceiver ∨ msg.flag == fCloseInitiator then do
      let locally := msg.flag == fCloseReceiver
      match (← s.streams.get).lookup (msg.id, locally) with
      | some st => do
        -- the peer closed its write side: our reads drain to EOF. Our
        -- writes stay open (half-close). If we had already closed too,
        -- the stream is fully done - retire it.
        st.pipe.close
        if !(← st.writeOpen.get) then
          s.removeStream (msg.id, locally)
      | none => pure ()
      pure true
    else if msg.flag == fResetReceiver ∨ msg.flag == fResetInitiator then do
      let locally := msg.flag == fResetReceiver
      -- reset: both directions die, the stream is retired
      match (← s.streams.get).lookup (msg.id, locally) with
      | some st => do
        st.writeOpen.set false
        st.pipe.close
        s.removeStream (msg.id, locally)
      | none => pure ()
      pure true
    else
      pure false

/-- The message pump: dispatch until EOF / protocol error. -/
partial def MplexSession.pump (s : MplexSession) : IO Unit := do
  match ← s.pumpOne with
  | false => pure ()
  | true => s.pump

end LeanP2P.Mplex
