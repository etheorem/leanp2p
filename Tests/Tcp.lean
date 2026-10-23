import Tests.Support

/-!
# TCP transport suite (VECTOR_TEST_PLAN.md, phase 4 step 23)

The phase 3 two-party exchanges replayed over real loopback TCP sockets
(`Std.Internal.UV.TCP`): raw echo with byte-stream semantics, full
multistream-select negotiations, the Noise XX handshake with post-handshake
transport round trips, and muxer negotiation (yamux, mplex) through the
upgrader. TCP itself is the "hostile transport": kernel segments split and
coalesce writes at will.
-/

open LeanP2P Tests

namespace Tests

private def loopback : Multiaddr :=
  match Multiaddr.parse? "/ip4/127.0.0.1/tcp/0" with
  | some a => a
  | none => { components := [] }

private def bytesOf (hex : String) : ByteArray :=
  match Bytes.ofHex? hex with
  | some b => b
  | none => ByteArray.empty

/-- Listen on an ephemeral loopback port, returning the listener. -/
private def withListener (f : Listener → IO Unit) : IO Unit := do
  let some l ← Tcp.listen loopback | throw <| IO.userError "tcp listen failed"
  try f l finally l.close

def TcpSuite.run (r : Runner) : IO Unit := do
  r.section "tcp transport"
    "(phase 4 step 23; loopback TCP via Std.Internal.UV.TCP - no upstream vectors)"

  /- raw echo over TCP: writes may split, reads are arbitrary prefixes -/
  withListener fun l => do
    let serverT ← IO.asTask do
      match ← l.accept with
      | none => pure ()
      | some c => do
        match ← c.read with
        | none => pure ()
        | some b => c.write b
        c.close
    let some c ← Tcp.dial l.addr | r.check "tcp dial" false; return ()
    c.write (Bytes.ofString "hello tcp")
    let got ← c.read
    r.check "tcp echo" (got == some (Bytes.ofString "hello tcp"))
    c.close
    let _ ← IO.wait serverT
    r.check "tcp dial" true
    r.check "tcp listener addr resolved" (l.addr != loopback)

  /- multistream-select over TCP: success, na, lazy dialer -/
  withListener fun l => do
    let serverT ← IO.asTask do
      -- serve one negotiation per iteration until the client goes away
      let rec serve : Connection → Nat → IO Unit
        | _, 0 => pure ()
        | c, n + 1 => do
          let rdr ← BufReader.ofConn c
          match ← Multiselect.selectResponder rdr c ["/ipfs/kad/1.0.0", "/ipfs/id/1.0.0"] with
          | none => c.close
          | some _ => serve c n  -- bounded fuel
      match ← l.accept with
      | none => pure ()
      | some c => serve c 4  -- at most 4 negotiations on one conn
    let some c ← Tcp.dial l.addr | r.check "tcp mss dial" false; return ()
    let rdr ← BufReader.ofConn c
    let got ← Multiselect.selectInitiator rdr c "/ipfs/kad/1.0.0"
    r.check "tcp mss select" (got == some "/ipfs/kad/1.0.0")
    let protos ← Multiselect.listProtocols rdr c
    r.check "tcp mss ls" (protos == some ["/ipfs/kad/1.0.0", "/ipfs/id/1.0.0"])
    c.close
    let _ ← IO.wait serverT
    r.check "tcp mss dial" true

  withListener fun l => do
    let serverT ← IO.asTask do
      match ← l.accept with
      | none => pure ()
      | some c => do
        let rdr ← BufReader.ofConn c
        let _ ← Multiselect.selectResponder rdr c ["/ipfs/kad/1.0.0"]
        c.close
    let some c ← Tcp.dial l.addr | r.check "tcp mss na dial" false; return ()
    let rdr ← BufReader.ofConn c
    let got ← Multiselect.selectInitiator rdr c "/nope/9.9.9"
    r.check "tcp mss na" (got == none)
    c.close
    let _ ← IO.wait serverT

  withListener fun l => do
    let serverT ← IO.asTask do
      match ← l.accept with
      | none => pure ()
      | some c => do
        let rdr ← BufReader.ofConn c
        let _ ← Multiselect.selectResponder rdr c ["/ipfs/kad/1.0.0"]
        c.close
    let some c ← Tcp.dial l.addr | r.check "tcp mss lazy dial" false; return ()
    let rdr ← BufReader.ofConn c
    let got ← Multiselect.selectInitiatorLazy rdr c "/ipfs/kad/1.0.0"
    r.check "tcp mss lazy" (got == some "/ipfs/kad/1.0.0")
    c.close
    let _ ← IO.wait serverT

  /- Noise XX over TCP with post-handshake transport round trips -/
  withListener fun l => do
    let idI : Keys.PrivKey :=
      { keyType := .ed25519, raw := bytesOf "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60" }
    let idR : Keys.PrivKey :=
      { keyType := .ed25519, raw := bytesOf "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb" }
    let some pubRk ← idR.publicKey | r.check "tcp noise keys" false; return ()
    let some staticI ← OpenSsl.randomBytes 32 | r.check "tcp noise keys" false; return ()
    let some staticR ← OpenSsl.randomBytes 32 | r.check "tcp noise keys" false; return ()
    let serverT ← IO.asTask do
      match ← l.accept with
      | none => pure ()
      | some c => do
        match ← Noise.handshake idR staticR .responder c with
        | none => c.close
        | some sc => do
          -- echo one transport message back, then finish
          match ← sc.read with
          | none => sc.close
          | some b => sc.write b; sc.close
    let some c ← Tcp.dial l.addr | r.check "tcp noise dial" false; return ()
    match ← Noise.handshake idI staticI .initiator c with
    | none => r.check "tcp noise handshake" false; c.close
    | some sc => do
      r.check "tcp noise handshake" true
      r.check "tcp noise initiator remote id" (sc.remotePeer == PeerId.ofPublicKey pubRk)
      sc.write (Bytes.ofString "secret over tcp")
      let got ← sc.read
      r.check "tcp noise transport round trip" (got == some (Bytes.ofString "secret over tcp"))
      sc.close
    let _ ← IO.wait serverT

  /- muxer negotiation + session over TCP: yamux -/
  withListener fun l => do
    let serverT ← IO.asTask do
      match ← l.accept with
      | none => pure ()
      | some c => do
        match ← Upgrade.muxResponder [YamuxChoice] none (← BufReader.ofConn c) with
        | none => c.close
        | some (_, h) => do
          match ← h.acceptStream with
          | none => h.shutdown
          | some s => do
            match ← s.read with
            | none => h.shutdown
            | some b => s.write b; s.close
            h.shutdown
    let some c ← Tcp.dial l.addr | r.check "tcp yamux dial" false; return ()
    match ← Upgrade.muxInitiator [YamuxChoice] none (← BufReader.ofConn c) with
    | none => r.check "tcp yamux upgrade" false; c.close
    | some (_, h) => do
      r.check "tcp yamux upgrade" true
      match ← h.openStream "/ipfs/ping/1.0.0" with
      | none => r.check "tcp yamux open" false
      | some s => do
        s.write (Bytes.ofString "yamux over tcp")
        let got ← s.read
        r.check "tcp yamux stream round trip" (got == some (Bytes.ofString "yamux over tcp"))
        s.close
      h.shutdown
      h.tasks.joinAll
    let _ ← IO.wait serverT

  /- muxer negotiation + session over TCP: mplex -/
  withListener fun l => do
    let serverT ← IO.asTask do
      match ← l.accept with
      | none => pure ()
      | some c => do
        match ← Upgrade.muxResponder [MplexChoice] none (← BufReader.ofConn c) with
        | none => c.close
        | some (_, h) => do
          match ← h.acceptStream with
          | none => h.shutdown
          | some s => do
            match ← s.read with
            | none => h.shutdown
            | some b => s.write b; s.close
            h.shutdown
    let some c ← Tcp.dial l.addr | r.check "tcp mplex dial" false; return ()
    match ← Upgrade.muxInitiator [MplexChoice] none (← BufReader.ofConn c) with
    | none => r.check "tcp mplex upgrade" false; c.close
    | some (_, h) => do
      r.check "tcp mplex upgrade" true
      match ← h.openStream "/ipfs/ping/1.0.0" with
      | none => r.check "tcp mplex open" false
      | some s => do
        s.write (Bytes.ofString "mplex over tcp")
        let got ← s.read
        r.check "tcp mplex stream round trip" (got == some (Bytes.ofString "mplex over tcp"))
        s.close
      h.shutdown
      h.tasks.joinAll
    let _ ← IO.wait serverT

  /- dialing a dead port fails cleanly -/
  let deadPort :=
    match Multiaddr.parse? "/ip4/127.0.0.1/tcp/1" with
    | some a => a
    | none => loopback
  let dead ← Tcp.dial deadPort
  r.check "tcp dial refused" dead.isNone

end Tests
