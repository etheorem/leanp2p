import LeanP2P.Net.Transport
import LeanP2P.Conn.Stream
import LeanP2P.Conn.Reader
import LeanP2P.Conn.Frame
import LeanP2P.Conc
import Std.Sync.Mutex
/-!
# Stream muxer

A framed muxer over any `Connection`: `[sid u32le][len u32le][payload]`.
Frame ids are odd for the dialing side, even for the listening side, like
yamux. Empty payload = EOF (half-close). The byte codec is the verified
`Framing` core; this module only does IO plumbing.

Phase 4 (step 22): stream pipes and the incoming-stream queue are blocking
`Chan`s (no polling); concurrent frame writes are serialized by a mutex;
the pump task is tracked and joined on shutdown.
-/

namespace LeanP2P

/-- A byte queue with EOF: blocking `read` (promise wake, no polling). -/
structure Pipe where
  ch : Chan ByteArray

def Pipe.new : IO Pipe := do
  return { ch := ← Chan.new }

/-- Blocks until a message or EOF (`none`). -/
def Pipe.read (p : Pipe) : IO (Option ByteArray) :=
  p.ch.recv

def Pipe.push (p : Pipe) (b : ByteArray) : IO Unit := do
  discard <| p.ch.send b

/-- Close the read side: unblocks the reader with EOF. -/
def Pipe.close (p : Pipe) : IO Unit :=
  p.ch.close

/-- An established mux session over one connection. Reads go through the
buffered reader the negotiation used (bytes over-read while selecting the
muxer are not lost). -/
structure MuxSession where
  conn : Connection
  reader : BufReader
  nextId : OnceRef Nat
  pending : OnceRef (List (Nat × Pipe))
  incoming : Chan Stream
  buf : IO.Ref (List Nat)
  dead : IO.Ref Bool
  writeMx : Std.Mutex Unit
  tasks : TaskSet

/-- 1 MiB per frame: a declared length above this is a protocol error,
not something to buffer. -/
def maxFrame : Nat := 1048576

def frameToBytes (f : Framing.Frame) : ByteArray :=
  Bytes.ofNatList (Framing.encode f)

/-- One frame per atomic write: concurrent stream writes must not
interleave half frames. -/
def MuxSession.writeFrame (m : MuxSession) (sid : Nat) (payload : ByteArray) : IO Unit :=
  m.writeMx.atomically fun _ => do
    m.conn.write (frameToBytes { sid := sid, payload := Bytes.toNatList payload })

def MuxSession.closeStream (m : MuxSession) (sid : Nat) : IO Unit := do
  match (← m.pending.get).lookup sid with
  | some p => p.close
  | none => pure ()

def MuxSession.streamOf (m : MuxSession) (sid : Nat) (p : Pipe) : Stream where
  read := p.read
  write := fun b => m.writeFrame sid b
  close := m.closeStream sid
  reset := do
    m.writeFrame sid ByteArray.empty
    match (← m.pending.get).lookup sid with
    | some pp => pp.close
    | none => pure ()

def MuxSession.openStream (m : MuxSession) : IO Stream := do
  let sid ← m.nextId.update fun n => (n + 2, n)
  let p ← Pipe.new
  m.pending.update fun ps => (ps ++ [(sid, p)], ())
  return (m.streamOf sid p)

/-- Close all stream pipes, the incoming queue and the connection. Idempotent. -/
def MuxSession.shutdown (m : MuxSession) : IO Unit := do
  unless ← m.dead.get do
    m.dead.set true
    for (_, p) in ← m.pending.get do
      p.close
    m.incoming.close
    m.conn.close

/-- Read frames off the connection and dispatch to stream pipes. -/
partial def MuxSession.drain (m : MuxSession) : IO Unit := do
  -- a declared length beyond the cap can never complete: protocol error
  match ← m.buf.get with
  | bs =>
    if bs.length > maxFrame + 8 then m.shutdown
    else match Framing.decode? bs with
    | none => pure ()
    | some (f, rest) =>
      m.buf.set rest
      if f.payload.isEmpty then
        match (← m.pending.get).lookup f.sid with
        | some p => p.close
        | none => pure ()
      else
        match (← m.pending.get).lookup f.sid with
        | some p => p.push (Bytes.ofNatList f.payload)
        | none =>
          let p ← Pipe.new
          p.push (Bytes.ofNatList f.payload)
          m.pending.update fun ps => (ps ++ [(f.sid, p)], ())
          discard <| m.incoming.send (m.streamOf f.sid p)
      MuxSession.drain m

partial def MuxSession.pumpLoop (m : MuxSession) : IO Unit := do
  -- buffered bytes first (negotiation over-reads), then fresh chunks
  match ← m.reader.readAvail with
  | none => m.shutdown
  | some chunk =>
    m.buf.set ((← m.buf.get) ++ Bytes.toNatList chunk)
    MuxSession.drain m
    MuxSession.pumpLoop m

def MuxSession.make (r : BufReader) (firstId : Nat) : IO MuxSession := do
  let m : MuxSession :=
    { conn := r.conn
      reader := r
      nextId := ← OnceRef.new firstId
      pending := ← OnceRef.new []
      incoming := ← Chan.new
      buf := ← IO.mkRef []
      dead := ← IO.mkRef false
      writeMx := ← Std.Mutex.new ()
      tasks := ← TaskSet.new }
  m.tasks.spawn (m.pumpLoop)
  return m

/-- Blocks until a remote stream arrives or the session dies. -/
def MuxSession.acceptStream (m : MuxSession) : IO (Option Stream) :=
  m.incoming.recv

/-- The muxer interface: client/server roles differ in stream-id parity.
Both roles mux the buffered reader they are given. -/
structure Muxer where
  name : String
  client : BufReader → IO (Option MuxSession)
  server : BufReader → IO (Option MuxSession)

def FramedMux : Muxer where
  name := "framed/1.0.0"
  client r := some <$> MuxSession.make r 1
  server r := some <$> MuxSession.make r 0

end LeanP2P
