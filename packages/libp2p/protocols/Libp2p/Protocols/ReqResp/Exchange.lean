import Conc
import Streams
import Libp2p.Protocols.Mock.Core
import Libp2p.Protocols.ReqResp.Core
import Libp2p.Protocols.ReqResp.Limiter

/-!
# Req/resp: the exchange

The IO shell over the reader core (ARCHITECTURE §3.3): one stream per
request, read through `Core.step` (phase0 `p2p-interface.md`,
"Req/Resp interaction": "We use ONE stream PER request/response
interaction"). The stream arrives negotiated, so the shell works on any
`Stream` value, and the suite drives it over the sim (PRINCIPLES 1.4).

* `request` is the requester. It writes the request, closes its write
  side ("The requester MUST close the write side"), and reads chunks
  until the core is done: the peer closed, an error chunk came, or
  `maxChunks` chunks came. Each chunk goes to `deliver` as it finishes,
  so a long response never sits in memory whole.
* `serve` is the responder. It reads the request to the end of the
  stream, answers a malformed one with an `InvalidRequest` chunk ("If
  steps (1), (2), or (3) fail ... the responder MUST respond in
  error"), writes the chunks of `respond`, and closes.
* `handler` wraps `serve` as the `StreamHandler` the host registers, and
  maps `Error` into the coarse core error once, at the seam (§3.5).
* `requestPeer` is the requester toward a peer: it takes a slot of the
  peer's `Limiter` (`MAX_CONCURRENT_REQUESTS`), opens the stream through
  the host's `OpenStream` call, and runs `request` on it. The call is an
  argument, so this module needs no host type.

## Deadlines

The spec leaves the requester's timeout to the client ("A typical
approach for the requester is to implement a timeout on the request that
depends on the nature of the request"), so each call takes `timeoutMs`.
The responder takes one for the read of the request, so a silent peer
cannot hold the stream (§5.4). The writes of the answer take none: a
responder may withhold chunks to rate-limit ("The responder MUST NOT
respond with an error or close the stream when rate limiting").

On expiry `withinDeadline` runs a `BaseIO` close. `Stream.reset` is
`Async`, so the expiry spawns the reset into a `TaskSet` the call owns,
and the call joins the set after the race (PRINCIPLES 3.2). The reset
resolves the parked `read`, which answers `.error .reset`, and the read
loop ends on it.

## The read loop

`pump` is `partial`: a peer may keep sending forever, and the bound is
the deadline, which resets the stream and so ends the parked read. That
is the standing reason for an IO read loop (CLAUDE.md, "`partial def`
only when termination really cannot be shown").
-/

set_option autoImplicit false

namespace Libp2p.Protocols.ReqResp

open Libp2p.Protocols
open Conc (Async)

/-- Hand out the chunks of a list of actions. -/
def deliverAll (deliver : Chunk → Async Unit) : List Core.Action → Async Unit
  | [] => pure ()
  | .chunk c :: rest => do deliver c; deliverAll deliver rest
  | .finished :: rest => deliverAll deliver rest

/-- Read the stream into the core until it is done or the stream ends.
The answer says whether the end of the stream came. Park: `s.read`,
which the peer's close, a reset, or the session's end wakes. -/
partial def pump (s : Streams.Stream) (st : Core.State) (deliver : Chunk → Async Unit) :
    Async (Except Error Bool) := do
  -- The requester stops at its last chunk; the responder waits for the end.
  if st.done ∧ st.config.side = .response then return .ok false
  match ← s.read with
  | .error e => return .error (.stream e)
  | .ok none =>
    match Core.step st .eof with
    | .error e => return .error e
    | .ok (_, acts) =>
      deliverAll deliver acts
      return .ok true
  | .ok (some b) =>
    match Core.step st (.bytes b) with
    | .error e => return .error e
    | .ok (st, acts) =>
      deliverAll deliver acts
      pump s st deliver

/-- Run `work` against a deadline that resets `s` on expiry. The reset
task lives in a set this call owns and joins. -/
def underDeadline {α : Type} (s : Streams.Stream) (clock : Conc.Clock) (ms : Nat)
    (work : Async (Except Error α)) : Async (Except Error α) := do
  let owner ← Conc.TaskSet.new
  let r ← Conc.withinDeadline clock ms (owner.spawn s.reset) work
  owner.joinAll
  match r with
  | .error .deadlineExpired => return .error .timeout
  | .error .closed => return .error (.stream .closed)
  | .ok a => return a

/-- The reader configuration of the requester. -/
def Method.responseConfig (m : Method) : Core.Config :=
  ⟨.response, m.response, m.contextLen, m.maxChunks⟩

/-- The reader configuration of the responder. -/
def Method.requestConfig (m : Method) : Core.Config :=
  ⟨.request, m.request.getD ⟨0, 0⟩, 0, 1⟩

/-- Send one request on `s` and hand each response chunk to `deliver`.
The stream is negotiated for `m.id`. A protocol error resets the stream
("they SHOULD reset the stream immediately"), and so does a stop before
the peer's end, since the rest of the response is no longer relevant. -/
def request (s : Streams.Stream) (m : Method) (clock : Conc.Clock) (timeoutMs : Nat)
    (payload : Option ByteArray) (deliver : Chunk → Async Unit) : Async (Except Error Unit) := do
  match encodeRequestB m payload with
  | .error e => return .error e
  | .ok bytes =>
    let work : Async (Except Error Bool) := do
      if 0 < bytes.size then
        if let .error e ← s.write bytes then return .error (.stream e)
      s.close
      pump s (Core.init m.responseConfig) deliver
    match ← underDeadline s clock timeoutMs work with
    | .ok true => return .ok ()
    | .ok false => s.reset; return .ok ()
    | .error e => s.reset; return .error e

/-- The host's call that opens a stream to one peer and negotiates one
of the ids, as go-libp2p's `NewStream` does. The caller binds the peer. -/
abbrev OpenStream :=
  List Mock.Core.ProtocolId → Async (Except Mock.Core.Error (Mock.Core.ProtocolId × Streams.Stream))

/-- Send one request to a peer: take a slot of the peer's `limiter`,
open the stream for `m.id` through the host, and run `request` on it.
The slot goes back on every path, a thrown fault included. -/
def requestPeer (openStream : OpenStream) (limiter : Limiter) (m : Method) (clock : Conc.Clock)
    (timeoutMs : Nat) (payload : Option ByteArray) (deliver : Chunk → Async Unit) :
    Async (Except Error Unit) := do
  if !(← limiter.take m.id) then return .error .tooManyRequests
  try
    match ← openStream [m.id] with
    | .error e => return .error (.openFailed e)
    | .ok (_, s) => request s m clock timeoutMs payload deliver
  finally
    limiter.give m.id

/-- `request`, with the chunks collected in order. For a response that
fits in memory, such as a single chunk. -/
def requestAll (s : Streams.Stream) (m : Method) (clock : Conc.Clock) (timeoutMs : Nat)
    (payload : Option ByteArray) : Async (Except Error (List Chunk)) := do
  let acc ← Conc.OnceRef.new ([] : List Chunk)
  match ← request s m clock timeoutMs payload (fun c => acc.update (c :: ·)) with
  | .error e => return .error e
  | .ok () => return .ok (← acc.get).reverse

/-- The error message of an `InvalidRequest` answer: the error's name,
which fits the 256-byte `ErrorMessage` limit. -/
def invalidRequestMessage (e : Error) : ByteArray :=
  (toString (repr e)).toUTF8.extract 0 Constants.errorMessageLimit

/-- Write the chunks of an answer, then close. A chunk the writer
refuses ends the answer with a `ServerError` chunk. -/
def writeAnswer (s : Streams.Stream) (m : Method) (chunks : List Chunk) :
    Async (Except Error Unit) := do
  for c in chunks do
    match encodeChunkB m c with
    | .ok bytes =>
      if let .error e ← s.write bytes then return .error (.stream e)
    | .error e =>
      let msg := invalidRequestMessage e
      if let .ok bytes := encodeChunkB m ⟨.serverError, ByteArray.empty, msg⟩ then
        if let .error e ← s.write bytes then return .error (.stream e)
      s.close
      return .error e
  s.close
  return .ok ()

/-- Serve one request on `s`. `respond` gets the payload (`none` for a
method with no request content) and gives the chunks to send. -/
def serve (s : Streams.Stream) (m : Method) (clock : Conc.Clock) (timeoutMs : Nat)
    (respond : Option ByteArray → Async (List Chunk)) : Async (Except Error Unit) := do
  let got ← Conc.OnceRef.new (none : Option ByteArray)
  let read : Async (Except Error Bool) :=
    pump s (Core.init m.requestConfig m.request.isSome) fun c => got.set (some c.payload)
  match ← underDeadline s clock timeoutMs read with
  | .error (.stream e) => return .error (.stream e)
  | .error .timeout => return .error .timeout
  | .error e =>
    -- A malformed request: answer in error, then close.
    if let .ok bytes := encodeChunkB m ⟨.invalidRequest, ByteArray.empty, invalidRequestMessage e⟩ then
      discard <| s.write bytes
    s.close
    return .error e
  | .ok _ =>
    let chunks ← respond (← got.get)
    writeAnswer s m chunks

/-- The one map from a req/resp error into the coarse core error. -/
def mapError : Error → Mock.Core.Error
  | .stream e => Mock.Core.mapStreamError e
  | .timeout => .timeout "req/resp: the deadline expired"
  | .openFailed e => e
  | e => .protocol s!"req/resp: {repr e}"

/-- The handler value the host registers under `m.id`. -/
def handler (m : Method) (clock : Conc.Clock) (timeoutMs : Nat)
    (respond : Option ByteArray → Async (List Chunk)) : Mock.Core.StreamHandler :=
  ⟨m.id, fun s => ExceptT.mk do return (← serve s m clock timeoutMs respond).mapError mapError⟩

end Libp2p.Protocols.ReqResp
