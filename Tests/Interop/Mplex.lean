import Libp2p.Mux

/-!
# The mplex interop driver (unit W5.10)

The Lean side of the mplex interop check against go-mplex v0.7.0.
go-libp2p v0.50 dropped mplex from its defaults, so the go side is
go-mplex itself. `scripts/mplex-interop.sh` builds the go side
(`scripts/mplex-interop/`) and runs both directions over loopback TCP,
plain: no security and no negotiation, so the check sees mplex
messages alone.

* `mplex-interop listen`: listen, print the port, accept one
  connection, and echo every stream: read to the peer's close, then
  write the bytes back and close.
* `mplex-interop dial PORT`: connect, open four streams at once, write
  past the 1 MiB message cap on each, half-close, and check the echo.

Both sides number their streams from zero, so the four streams of the
dialer meet the identity rule of `Mplex/State.lean` on the wire. The
payload is `mplexMessageCap + 7` bytes, so the Lean side splits each
write in two messages, and the go side reads a message of exactly the
cap.

The driver lives outside `lake test`, which stays hermetic: Go tooling
is test-only and confined to the harness (CLAUDE.md, "Dependencies").
The payload pattern matches the go side.
-/

set_option autoImplicit false

namespace Tests.Interop.Mplex

open Conc Streams Libp2p.Core Libp2p.Mux

/-- The streams the dialer opens at once. -/
def streams : Nat := 4

/-- The bytes per stream: past the message cap, so a write splits. -/
def size : Nat := mplexMessageCap + 7

/-- The pattern for stream `i`, as the go side builds it. -/
def payload (i n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun k => UInt8.ofNat ((k * 7 + i * 13) % 251)⟩

/-- Every byte of a stream until its end, or the error that ended it. -/
def readAll (s : Stream) : Async (Except Streams.Error ByteArray) := do
  let mut acc := ByteArray.empty
  repeat
    match ← s.read with
    | .ok (some c) => acc := acc ++ c
    | .ok none => return .ok acc
    | .error e => return .error e
  return .ok acc

/-- A multiaddr from its text form. -/
def addr (s : String) : Async Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"bad address {s}"

/-- Fail with a message. -/
def fail {α : Type} (msg : String) : Async α :=
  throw <| IO.userError s!"lean: {msg}"

/-- The session's answer, as a fault when it is an error. -/
def joinOk (s : MuxSession) : Async Unit := do
  match ← s.join.run with
  | .ok () => return ()
  | .error e => fail s!"the session ended with {repr e}"

/-- The session `Mux.mplex.open` returns. -/
def openSession (role : Role) (conn : Connection) : Async MuxSession := do
  match ← (mplex.open role conn .empty Conc.Clock.system).run with
  | .ok s => return s
  | .error e => fail s!"open: {repr e}"

/-- The listener side: accept one connection, and echo every stream
after the peer's close. It fails unless the peer opened exactly
`streams` streams and each echo went through. -/
def listenMode : Async Unit := do
  let l ← Tcp.transport.listen (← addr "/ip4/127.0.0.1/tcp/0")
  let some port := Tcp.socketAddress? l.addr |>.map (·.port) | fail "no port"
  IO.println port
  (← IO.getStdout).flush
  let some conn ← l.accept | fail "accept failed"
  l.close
  let session ← openSession .responder conn
  let tasks ← TaskSet.new
  let failures : OnceRef (List String) ← OnceRef.new []
  let mut accepted := 0
  repeat
    -- Park: the peer's next stream, or the end of the session.
    let some st ← session.accept | break
    accepted := accepted + 1
    tasks.spawn do
      match ← readAll st with
      | .ok data =>
        match ← st.write data with
        | .ok () => st.close
        | .error e => failures.update (s!"write: {repr e}" :: ·)
      | .error e => failures.update (s!"read: {repr e}" :: ·)
  tasks.joinAll
  joinOk session
  l.join
  if accepted != streams then failures.update (s!"accepted {accepted} streams, want {streams}" :: ·)
  match ← (failures.get : BaseIO (List String)) with
  | [] => return ()
  | fs => fail s!"{fs}"

/-- The dialer side: connect, open `streams` streams at once, write
`size` bytes on each, half-close, and compare the echo. -/
def dialMode (port : String) : Async Unit := do
  let some conn ← Tcp.transport.dial (← addr s!"/ip4/127.0.0.1/tcp/{port}") | fail "dial failed"
  let session ← openSession .initiator conn
  let tasks ← TaskSet.new
  let failures : OnceRef (List String) ← OnceRef.new []
  for i in [0:streams] do
    tasks.spawn do
      let .ok st ← (session.openStream mplexId).run | failures.update (s!"open {i}" :: ·)
      let want := payload i size
      match ← st.write want with
      | .error e => failures.update (s!"write {i}: {repr e}" :: ·)
      | .ok () =>
        st.close
        match ← readAll st with
        | .ok got =>
          if got != want then failures.update (s!"stream {i}: echo of {want.size} differs, got {got.size}" :: ·)
        | .error e => failures.update (s!"read {i}: {repr e}" :: ·)
  tasks.joinAll
  session.close
  joinOk session
  match ← (failures.get : BaseIO (List String)) with
  | [] => return ()
  | fs => fail s!"{fs}"

end Tests.Interop.Mplex

def main (args : List String) : IO UInt32 := do
  let run : Conc.Async Unit := match args with
    | ["listen"] => Tests.Interop.Mplex.listenMode
    | ["dial", port] => Tests.Interop.Mplex.dialMode port
    | _ => Tests.Interop.Mplex.fail "usage: mplex-interop listen | dial PORT"
  try
    run.run
    IO.eprintln "lean: ok"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
