import Conc
import InteropHostname
import Libp2p.Identity
import Libp2p.Protocols.Gossipsub.Interop

/-! Host-free participant core. Host wiring stays provisional until the green interfaces settle. -/
set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Interop

open Libp2p.Identity

/-- Parse the harness command line. -/
def paramsPath (args : List String) : Except String System.FilePath :=
  match args with
  | ["--params", path] => .ok path
  | _ => .error "expected --params <path>"

/-- Prefer the hostname syscall. Environment variables are a fallback. -/
def processHostname : IO String := do
  let hostname ← try
    InteropHostname.get
  catch e =>
    IO.eprintln s!"gethostname failed: {e}; trying environment"
    pure ""
  if (nodeId? hostname).isSome then return hostname
  if !hostname.isEmpty then
    IO.eprintln s!"gethostname returned '{hostname}', not nodeN; trying environment"
  let value ← IO.getEnv "HOSTNAME"
  let fallback ← IO.getEnv "COMPUTERNAME"
  if let some name := value then
    if (nodeId? name).isSome then return name
  if let some name := fallback then
    if (nodeId? name).isSome then return name
  throw (IO.userError "hostname is not nodeN in syscall or environment")

/-- The 1 MiB RPC body leaves room for protobuf envelope overhead. -/
def maxPayloadBytes : Int := 1048576 - 1024

/-- Encode an id as eight big-endian bytes, then zero-pad to the requested size. -/
def publishPayload (messageId size : Int) : Except String ByteArray := do
  if messageId < 0 || messageId > 18446744073709551615 then
    throw "publish.messageID must fit UInt64"
  if size < 8 then throw "publish.messageSizeBytes must be at least eight"
  if size > maxPayloadBytes then throw "publish.messageSizeBytes exceeds the 1 MiB RPC budget"
  let id := messageId.toNat
  let head := (List.range 8).map fun i => UInt8.ofNat ((id / (2 ^ (8 * (7 - i)))) % 256)
  return ByteArray.mk (head.toArray ++ Array.replicate (size.toNat - 8) 0)

/-- Derive the deterministic identity and peer id for nodeN. -/
def identityForNode (nodeId : Nat) : Except String (PrivKey × PeerId) := do
  let seed := ByteArray.mk ((peerSeed nodeId).map UInt8.ofNat).toArray
  let key ← (PrivKey.ed25519OfData? seed).mapError (fun e => reprStr e)
  let pub ← key.toPublic.mapError (fun e => reprStr e)
  let peer ← (PeerId.ofPubKey pub).mapError (fun e => reprStr e)
  return (key, peer)

/-- A bounded stdout owner. Observers only offer complete lines. -/
structure RecordWriter where
  records : Conc.Chan String
  tasks : Conc.TaskSet
  failed : Conc.OnceRef (Option String)

namespace RecordWriter

def start : BaseIO RecordWriter := do
  let records ← Conc.Chan.new 64
  let tasks ← Conc.TaskSet.new
  let failed ← Conc.OnceRef.new (none : Option String)
  tasks.spawn <| do
    repeat
      match ← records.recv with
      | none => break
      | some line =>
        try
          IO.println line
          (← IO.getStdout).flush
        catch e =>
          failed.update (fun old => old.orElse (fun _ => some (toString e)))
          records.close
          break
  return { records, tasks, failed }

def offer (writer : RecordWriter) (line : String) : BaseIO Bool := do
  let ok ← writer.records.trySend line
  if !ok then writer.failed.update (fun old => old.orElse (fun _ => some "record queue full or closed"))
  return ok

def close (writer : RecordWriter) : Conc.Async Unit := do
  writer.records.close
  writer.tasks.joinAll
  if let some error ← writer.failed.get then throw (IO.userError error)

end RecordWriter

/-- Build the PeerID NDJSON record before any receipt. -/
def peerRecord (time peer : String) (nodeId : Nat) : String :=
  peerIdLine time peer (Int.ofNat nodeId)

/-- Build a pre-deduplication receipt record. -/
def receivedRecord (time : String) (payload : List Nat) (sender topic : Option String) : String :=
  receivedMessageLine time (messageIdNumber payload) sender topic

/-- Topic validation delays are updated in one atomic step. -/
structure DelayTable where
  entries : Conc.OnceRef (List (String × Nat))
  stopping : Conc.Chan Unit

/-- Create the delay table and its shutdown signal. -/
def DelayTable.new : BaseIO DelayTable := do
  return ⟨← Conc.OnceRef.new [], ← Conc.Chan.new 1⟩

/-- Replace one topic's delay. -/
def DelayTable.set (table : DelayTable) (topic : String) (delay : Nat) : BaseIO Unit :=
  table.entries.update fun entries => (topic, delay) :: entries.filter (fun entry => entry.1 != topic)

/-- The delay for a batch is the largest delay of its published topics. -/
def DelayTable.batchDelay (entries : List (String × Nat)) (topics : List String) : Nat :=
  topics.foldl (fun longest topic => max longest ((entries.find? (fun entry => entry.1 == topic)).map Prod.snd |>.getD 0)) 0

/-- Park a stream reader until its delay ends or shutdown starts. -/
def DelayTable.wait (table : DelayTable) (clock : Conc.Clock) (topics : List String) : Conc.Async Unit := do
  let delay := batchDelay (← table.entries.get) topics
  if delay > 0 then
    let timer ← (clock.after delay : BaseIO (Conc.Park Unit))
    Conc.select #[timer, Conc.Park.recv table.stopping (fun _ => ())]

/-- Counted pre-deduplication receipt observer. It never parks. -/
structure ReceiptObserver where
  writer : RecordWriter
  offers : Conc.OnceRef Nat
  failures : Conc.OnceRef Nat

/-- Create receipt accounting state. -/
def ReceiptObserver.new (writer : RecordWriter) : BaseIO ReceiptObserver := do
  return { writer, offers := ← Conc.OnceRef.new 0, failures := ← Conc.OnceRef.new 0 }

/-- Format a natural number with at least two decimal digits. -/
def pad2 (value : Nat) : String :=
  let text := String.ofList (Nat.toDigits 10 value)
  if text.length = 1 then "0" ++ text else text

/-- Format a natural number with at least three decimal digits. -/
def pad3 (value : Nat) : String :=
  let text := String.ofList (Nat.toDigits 10 value)
  if text.length = 1 then "00" ++ text
  else if text.length = 2 then "0" ++ text
  else text

/-- RFC3339 UTC time from the monotonic millisecond clock. -/
def observationTime : BaseIO String := do
  let nowMs ← IO.monoMsNow
  let secs := (nowMs / 1000) % 86400
  let ms := nowMs % 1000
  let hours := secs / 3600
  let minutes := (secs / 60) % 60
  let seconds := secs % 60
  return "1970-01-01T" ++ pad2 hours ++ ":" ++ pad2 minutes ++ ":" ++
    pad2 seconds ++ "." ++ pad3 ms ++ "Z"

/-- Decode one RPC and offer one receipt for every publish entry. -/
def ReceiptObserver.onRpc (observer : ReceiptObserver) (sender : String) (bytes : List Nat) : BaseIO Unit := do
  match Core.decodeRpc bytes with
  | .error _ => observer.failures.update (· + 1)
  | .ok rpc =>
    for message in rpc.publish do
      let time ← observationTime
      let payload := message.data.getD []
      let line := receivedRecord time payload (some sender) (some message.topic.name)
      observer.offers.update (· + 1)
      if !(← observer.writer.offer line) then observer.failures.update (· + 1)

/-- Count receipt failures. The supervisor uses this before exit 0. -/
def ReceiptObserver.failureCount (observer : ReceiptObserver) : BaseIO Nat := observer.failures.get

/-- Provisional future Node.Config.beforeRpc hook. The current Node has no field. -/
def provisionalBeforeRpc (table : DelayTable) (clock : Conc.Clock) (_sender : Peer) (bytes : List Nat) : Conc.Async Unit := do
  match Core.decodeRpc bytes with
  | .error _ => pure ()
  | .ok rpc => table.wait clock (rpc.publish.map (·.topic.name))

/-- Provisional BaseIO callback shape for Node.Config.beforeRpc. -/
def provisionalOnRpc (observer : ReceiptObserver) (sender : String) (bytes : List Nat) : BaseIO Unit :=
  observer.onRpc sender bytes

/-- Host-free callbacks used by the script driver. -/
structure Driver where
  connect : Int → Conc.Async (Except String Unit) := fun _ => pure (.error "host wiring is provisional")
  subscribe : String → Bool → BaseIO Bool := fun _ _ => pure false
  publish : String → ByteArray → BaseIO Bool := fun _ _ => pure false
  validationDelay : String → Nat → BaseIO Unit := fun _ _ => pure ()

/-- Execute selected instructions. waitUntil parks only this script computation. -/
def runScript (driver : Driver) (clock : Conc.Clock) (start : Nat) (actions : List Instruction) : Conc.Async (Except String Unit) := do
  for action in actions do
    let result ← match action with
    | .connect peers =>
        let mut outcome : Except String Unit := .ok ()
        for peer in peers do
          if outcome.isOk then outcome ← driver.connect peer
        pure outcome
    | .subscribeToTopic topic isPartial =>
        if ← driver.subscribe topic isPartial then pure (.ok ()) else pure (.error "subscribe queue refused")
    | .publish id size topic => do
        match publishPayload id size with
        | .error e => pure (.error e)
        | .ok bytes =>
          if ← driver.publish topic bytes then pure (.ok ()) else pure (.error "publish queue refused")
    | .setTopicValidationDelay topic seconds =>
        driver.validationDelay topic (Float.floor (seconds * 1000.0)).toUInt64.toNat
        pure (.ok ())
    | .waitUntil deadline =>
        repeat
          let now ← (clock.nowMs : BaseIO Nat)
          let due := start + deadline.toNat * 1000
          if now >= due then break
          let left := due - now
          let timer ← (clock.after left : BaseIO (Conc.Park Unit))
          discard <| Conc.select #[timer]
        pure (.ok ())
    | .initGossipSub _ => pure (.error "unexpected initGossipSub after startup")
    | .ifNodeIDEquals _ _ => pure (.error "unresolved node condition")
    if let .error error := result then return .error error
  return .ok ()

end Libp2p.Protocols.Gossipsub.Interop
