import Yamux

/-!
# The yamux interop driver (unit W4.3)

The Lean side of the yamux interop check against go-yamux v5.1.0, the
version go-libp2p v0.50 pins. `scripts/yamux-interop.sh` builds the go
side (`scripts/yamux-interop/`) and runs both directions over loopback
TCP, plain: no security and no negotiation, so the check sees yamux
frames alone. The full stack meets go-libp2p at W5.9.

* `yamux-interop listen`: listen, print the port, accept one connection
  as the server, and echo every stream: read to the peer's FIN, then
  write the bytes back and close.
* `yamux-interop dial PORT`: connect as the client, ping, open four
  streams at once, write past the window on each, half-close, and check
  the echo.

The driver lives outside `lake test`, which stays hermetic: Go tooling
is test-only and confined to the harness (CLAUDE.md, "Dependencies").
The payload pattern matches the go side.
-/

set_option autoImplicit false

namespace Tests.Interop

open Conc Streams Yamux

/-- The streams the dialer opens at once. -/
def streams : Nat := 4

/-- The bytes per stream: past the 256 KiB window, so flow control runs. -/
def size : Nat := 1048576 + 7

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
def joinOk (s : Session) : Async Unit := do
  match ← s.join with
  | .ok () => return ()
  | .error e => fail s!"the session ended with {repr e}"

/-- The listener side: accept one connection as the server, and echo
every stream after the peer's FIN. It fails unless the peer opened
exactly `streams` streams and each echo went through, so a dialer that
opens none cannot pass this side. -/
def listenMode : Async Unit := do
  let l ← Tcp.transport.listen (← addr "/ip4/127.0.0.1/tcp/0")
  let some port := Tcp.socketAddress? l.addr |>.map (·.port) | fail "no port"
  IO.println port
  (← IO.getStdout).flush
  let some conn ← l.accept | fail "accept failed"
  l.close
  let session ← Session.new .server conn
  let tasks ← TaskSet.new
  let failures : OnceRef (List String) ← OnceRef.new []
  let mut accepted := 0
  repeat
    -- Park: the peer's next stream, or the end of the session.
    let some st ← session.acceptStream | break
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

/-- The dialer side: connect as the client, ping, open `streams`
streams at once, write `size` bytes on each past the window, half-close,
and compare the echo. -/
def dialMode (port : String) : Async Unit := do
  let some conn ← Tcp.transport.dial (← addr s!"/ip4/127.0.0.1/tcp/{port}") | fail "dial failed"
  let session ← Session.new .client conn
  match ← session.ping with
  | .ok () => pure ()
  | .error e => fail s!"ping: {repr e}"
  let tasks ← TaskSet.new
  let failures : OnceRef (List String) ← OnceRef.new []
  for i in [0:streams] do
    tasks.spawn do
      let .ok st ← session.openStream | failures.update (s!"open {i}" :: ·)
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

end Tests.Interop

def main (args : List String) : IO UInt32 := do
  let run : Conc.Async Unit := match args with
    | ["listen"] => Tests.Interop.listenMode
    | ["dial", port] => Tests.Interop.dialMode port
    | _ => Tests.Interop.fail "usage: yamux-interop listen | dial PORT"
  try
    run.run
    IO.eprintln "lean: ok"
    return 0
  catch e =>
    IO.eprintln s!"{e}"
    return 1
