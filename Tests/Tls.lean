import Tests.Support
import Crypto
import Streams
import Tls
import TlsNative
import Libp2p.Identity
import Libp2p.Core
import Libp2p.Security
import Libp2p.Mux
import Libp2p.Negotiate

/-!
# The libp2p TLS suite (unit W5.11)

The checks of `packages/libp2p/security/docs/PLAN.md`, "Test milestones
(unit 2)", over `tls-ext.json`, the four certificates of the TLS spec
(tls.md, "Test vectors"), and over handshakes between two engines on
the sim transport:

* the spec vectors: each valid certificate derives the spec's peer id,
  and the invalid one fails its signature check, as the spike's
  `Tests/TlsExt.lean` checked them;
* the validity window, which the spike did not check;
* the extension rules, one `CertError` arm each, over the generated
  certificates of `backend-strictness.json`;
* the `SignedKey` codec: the spec values read back and re-encode to
  their bytes, and every non-shortest DER form is refused;
* certificates we issue, for each host key type, and the refusals of
  each check of `Tls.verify`;
* the test value: fixed keys and a fixed clock repeat the peer ids;
* the handshake in both roles, with data both ways, and its refusals:
  an expired certificate, a failed clock read, a certificate without
  the extension, a client without the ALPN name, and a chain of two
  certificates, each with the alert or the close that the peer sees;
* the records and the close of `net/tls`: a KeyUpdate in both
  directions, a record that fails to decrypt and its alert, the
  `close_notify` of `close`, no alert from `abort` or from a close
  during a parked write, and the end of the connection at and inside
  a record;
* the upgrade with `/tls/1.0.0` and yamux, and an unexpected peer.
-/

set_option autoImplicit false

namespace Tests.TlsSuite

open Conc Streams Libp2p.Identity Libp2p.Core
open Libp2p.Security

/-- A time inside the validity of the spec vectors, 2027-01-15. -/
private def vectorNow : Int := 1800000000

/-- `n` bytes of the value `v`. -/
private def fill (n : Nat) (v : UInt8) : ByteArray := ⟨Array.replicate n v⟩

/-- The value of an `Except`, or a failed run. -/
private def expectOk {ε α : Type} [Repr ε] (where_ : String) : Except ε α → IO α
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{where_}: {repr e}"

/-- The bytes of a hex string, or a failed run. -/
private def hexOf (where_ h : String) : IO ByteArray :=
  match Bytes.ofHex? h with
  | some b => pure b
  | none => throw <| IO.userError s!"{where_}: bad hex"

/-! ## The spec vectors -/

private def vectors (r : Runner) : IO Unit := do
  let file := "tls-ext.json"
  let j ← loadJson file
  for c in ← jArr file j "cases" do
    let name ← jStr file c "name"
    let cert ← hexOf name (← jStr file c "certHex")
    match ← jStr? file c "peerId", Tls.verify cert vectorNow with
    | some want, .ok v =>
      r.check s!"tls {name}: the certificate derives the peer id {want}" (v.peer.toString == want)
    | some _, .error e =>
      r.check s!"tls {name}: the certificate is accepted ({e})" false
    | none, res =>
      r.check s!"tls {name}: the certificate fails its signature check"
        (res matches .error .signature)
    -- The extension value reads back and re-encodes to its own bytes:
    -- the spec values are shortest-form DER.
    match Crypto.inspect cert Tls.extensionOid with
    | .ok ci =>
      let raw := Bytes.toNatList ci.extension
      r.check s!"tls {name}: the SignedKey re-encodes to its bytes"
        ((Tls.SignedKey.decode? raw).map (·.encode) == some raw)
    | .error _ => r.check s!"tls {name}: the extension parses" false
  -- The window: the vectors hold NotBefore 1975 and NotAfter 4096.
  let cert ← hexOf "window" ((← jStr file ((← jArr file j "cases").head!) "certHex"))
  r.check "tls window: a time before NotBefore is not yet valid"
    (Tls.verify cert 0 matches .error .notYetValid)
  r.check "tls window: a time after NotAfter has expired"
    (Tls.verify cert 100000000000 matches .error .expired)
  -- Both ends belong to the window (RFC 5280 §4.1.2.5): NotBefore is
  -- 1975-01-01 13:00:00 UTC, and NotAfter is 4096-01-01 13:00:00 UTC.
  r.check "tls window: NotBefore itself is valid" (Tls.verify cert 157813200 matches .ok _)
  r.check "tls window: one second before NotBefore is not yet valid"
    (Tls.verify cert 157813199 matches .error .notYetValid)
  r.check "tls window: NotAfter itself is valid" (Tls.verify cert 67090165200 matches .ok _)
  r.check "tls window: one second after NotAfter has expired"
    (Tls.verify cert 67090165201 matches .error .expired)

/-- The extension rules, one `CertError` arm each, over the generated
certificates of the backend suite: their required OID is the libp2p
one (`scripts/gen-backend-fixtures.py`). -/
private def extensionRules (r : Runner) : IO Unit := do
  let file := "backend-strictness.json"
  let j ← loadFixture file
  let cert (name : String) : IO ByteArray := do
    for c in ← jArr file j "certificates" do
      if (← jStr file c "name") == name then
        return ← hexOf name (← jStr file c "certHex")
    throw <| IO.userError s!"{file}: no certificate {name}"
  r.check "tls verify: an unknown critical extension is refused"
    (Tls.verify (← cert "unknownCritical") vectorNow matches .error .unknownCriticalExtension)
  r.check "tls verify: an extension that appears twice is refused"
    (Tls.verify (← cert "duplicateExtension") vectorNow matches .error .duplicateExtension)
  r.check "tls verify: a certificate without the extension is refused"
    (Tls.verify (← cert "missingExtension") vectorNow matches .error .missingExtension)
  r.check "tls verify: bytes that are no certificate are refused"
    (Tls.verify (fill 8 0) vectorNow matches .error .malformed)

/-! ## The `SignedKey` codec -/

private def codec (r : Runner) : IO Unit := do
  let sk : Tls.SignedKey := { publicKey := List.replicate 300 7, signature := List.replicate 70 9 }
  r.check "signedkey: a value with a two-byte length reads back"
    ((sk.encode?).bind Tls.SignedKey.decode? == some sk)
  r.check "signedkey: a value past the cap has no encoding"
    (({ publicKey := List.replicate 70000 1, signature := [] } : Tls.SignedKey).encode? == none)
  let good := [0x30, 0x06, 0x04, 0x01, 0xAA, 0x04, 0x01, 0xBB]
  r.check "signedkey: the shortest form reads"
    (Tls.SignedKey.decode? good == some ⟨[0xAA], [0xBB]⟩)
  r.check "signedkey: a byte after the SEQUENCE is refused"
    (Tls.SignedKey.decode? (good ++ [0]) == none)
  r.check "signedkey: a byte after the second OCTET STRING is refused"
    (Tls.SignedKey.decode? [0x30, 0x07, 0x04, 0x01, 0xAA, 0x04, 0x01, 0xBB, 0x00] == none)
  r.check "signedkey: a long form for a short length is refused"
    (Tls.SignedKey.decode? [0x30, 0x81, 0x06, 0x04, 0x01, 0xAA, 0x04, 0x01, 0xBB] == none)
  r.check "signedkey: a two-byte length with a leading zero is refused"
    (Tls.decodeLength [0x82, 0x00, 0xFF] == none)
  r.check "signedkey: the indefinite form is refused"
    (Tls.decodeLength [0x80] == none)
  r.check "signedkey: three length bytes are refused"
    (Tls.decodeLength [0x83, 0x01, 0x00, 0x00] == none)
  r.check "signedkey: a length past the input is refused"
    (Tls.SignedKey.decode? [0x30, 0x10, 0x04, 0x01, 0xAA] == none)
  r.check "signedkey: another outer tag is refused"
    (Tls.SignedKey.decode? [0x31, 0x06, 0x04, 0x01, 0xAA, 0x04, 0x01, 0xBB] == none)

/-! ## Our certificates -/

/-- An Ed25519 host key from one byte. -/
private def ed25519Key (v : UInt8) : IO PrivKey :=
  expectOk "ed25519 key" (PrivKey.ofData? .ed25519 (fill 32 v))

/-- The host keys of every type the identity package signs with. -/
private def hostKeys : IO (List (String × PrivKey)) := do
  let secp ← expectOk "secp256k1 key" (PrivKey.ofData? .secp256k1 (fill 32 3))
  let ecdsa ← expectOk "ecdsa key" (← Crypto.p256Generate.run)
  let rsa ← expectOk "rsa key" (← (Crypto.rsaGenerate 2048).run)
  return [("ed25519", ← ed25519Key 1), ("secp256k1", secp),
    ("ecdsa", ← expectOk "ecdsa key" (PrivKey.ofData? .ecdsa ecdsa)),
    ("rsa", ← expectOk "rsa key" (PrivKey.ofData? .rsa rsa))]

private def issued (r : Runner) : IO Unit := do
  let now ← Tls.wallSeconds
  for (name, key) in ← hostKeys do
    let want ← expectOk name (key.toPublic.bind PeerId.ofPubKey)
    match ← (Tls.Identity.generate key now).run with
    | .ok id =>
      match Tls.verify id.certificate now with
      | .ok v => r.check s!"tls issue {name}: our certificate derives our peer id" (v.peer == want)
      | .error e => r.check s!"tls issue {name}: our certificate verifies ({e})" false
    | .error e => r.check s!"tls issue {name}: the certificate issues ({e})" false
  -- The refusals of `verify`, one per check.
  let key ← ed25519Key 1
  let certKey ← expectOk "cert key" (← Crypto.p256Generate.run)
  let spki ← expectOk "spki" (Crypto.p256PublicKey certKey)
  let pub ← expectOk "pub" key.toPublic
  let sig ← expectOk "sig" (← (key.sign (Tls.signedData spki)).run)
  let sk : Tls.SignedKey := ⟨Bytes.toNatList pub.marshal, Bytes.toNatList sig⟩
  let value := Bytes.ofNatList sk.encode
  let issue (oid : String) (v : ByteArray) (critical : Bool) : IO ByteArray := do
    expectOk "issue" (← (Crypto.issue certKey oid v critical (now - 60) (now + 3600)).run)
  r.check "tls verify: a critical libp2p extension is accepted"
    (Tls.verify (← issue Tls.extensionOid value true) now matches .ok _)
  r.check "tls verify: our certificate under another OID lacks the extension"
    (Tls.verify (← issue "1.3.6.1.4.1.53594.1.2" value false) now matches .error .missingExtension)
  r.check "tls verify: an extension that holds no SignedKey is refused"
    (Tls.verify (← issue Tls.extensionOid (value.push 0) false) now matches .error .extension)
  let other ← ed25519Key 2
  let otherSig ← expectOk "sig" (← (other.sign (Tls.signedData spki)).run)
  let forged := Bytes.ofNatList ({ sk with signature := Bytes.toNatList otherSig } : Tls.SignedKey).encode
  r.check "tls verify: a signature of another key is refused"
    (Tls.verify (← issue Tls.extensionOid forged false) now matches .error .signature)
  let badKey := Bytes.ofNatList ({ sk with publicKey := [1, 2, 3] } : Tls.SignedKey).encode
  r.check "tls verify: a public key that does not unmarshal is refused"
    (Tls.verify (← issue Tls.extensionOid badKey false) now matches .error (.publicKey _))
  let good ← issue Tls.extensionOid value false
  -- The last byte belongs to the signature, so the change breaks the
  -- self-signature and leaves the DER whole.
  let tampered := good.set! (good.size - 1) (good.get! (good.size - 1) ^^^ 1)
  r.check "tls verify: a changed signature byte fails the self-signature"
    (Tls.verify tampered now matches .error .selfSignature)

/-! ## The handshake -/

/-- An address, or a failed run. -/
private def ma (s : String) : Async Multiformats.Multiaddr := do
  match Multiformats.Multiaddr.parse? s with
  | .ok a => return a
  | .error _ => throw <| IO.userError s!"test address {s} does not parse"

/-- A connected pair over a fresh sim net: the dialer's end and the
listener's end. -/
private def pair (split : Bool := false) : Async (Connection × Connection) := do
  let net ← Streams.Sim.Net.new split
  let l ← net.transport.listen (← ma "/memory/11")
  let some c ← net.transport.dial l.addr | throw <| IO.userError "dial failed"
  let some s ← l.accept | throw <| IO.userError "accept failed"
  l.close
  return (c, s)

/-- A fixed P-256 certificate key, SEC1 DER (`openssl ecparam -name
prime256v1 -genkey -noout -outform DER`, once). -/
private def fixedCertKey : IO ByteArray :=
  hexOf "fixed cert key" <|
    "30770201010420f724d5da9aeb47b6cb6a9542f93fdb6263d292a4e19317ee13" ++
    "2c9e2d96de5bc9a00a06082a8648ce3d030107a14403420004f12f899cc42de2" ++
    "cca23ab0a272cbd59dbe01ba9d9a289023c823ce5991870ba6e95a8639ed81e7" ++
    "c5900492dee9b3c84c320bf42e28396490317a028093a95d27"

/-- The fixed configuration (`Tls.Config.fixed`) for an Ed25519 host key
from one byte, issued and checking at `now`. -/
private def cfgOf (v : UInt8) (now : Int := vectorNow) : IO Tls.Config := do
  expectOk "tls config" (← Tls.Config.fixed (← ed25519Key v) (← fixedCertKey) now)

/-- The check of a test client or server that takes any certificate. -/
private def acceptAny (_ : ByteArray) : Option String := none

/-- libssl's text for a received `bad_certificate` alert (the reason
string of `SSL_R_SSLV3_ALERT_BAD_CERTIFICATE`). -/
private def badCertificateText : String := "alert bad certificate"

/-- True when `text` holds `part`. -/
private def mentions (text part : String) : Bool := (text.splitOn part).length > 1

/-- True when a handshake failed on the peer's alert `bad_certificate`:
a protocol error whose text is libssl's for that alert. -/
private def gotAlert (res : Except Libp2p.Core.Error SecureConn) : Bool :=
  match res with
  | .error (.protocol d) => mentions d badCertificateText
  | _ => false

/-- `conn`, with each write counted in `n` before it runs. -/
private def counting (conn : Connection) (n : OnceRef Nat) : Connection :=
  { conn with write := fun b => do n.update (· + 1); conn.write b }

/-- Read until `n` bytes have arrived, or the end. -/
private def readConn (c : Connection) (n : Nat) : Async ByteArray := do
  let mut acc := ByteArray.empty
  while acc.size < n do
    match ← c.read with
    | some b => acc := acc ++ b
    | none => break
  return acc

/-- Both engine handshakes over `c` and `s`, with checks that take any
certificate: the responder as a task, the initiator here. -/
private def engineBoth (cfgI cfgR : Tls.Config) (c s : Connection) :
    Async (Except _root_.Tls.Error _root_.Tls.Secured × Except _root_.Tls.Error _root_.Tls.Secured) := do
  let t ← (Conc.Wrap.spawn (_root_.Tls.handshake cfgR.context true s .empty acceptAny) :
    BaseIO (Task (Except IO.Error (Except _root_.Tls.Error _root_.Tls.Secured))))
  let ri ← _root_.Tls.handshake cfgI.context false c .empty acceptAny
  match ← Conc.Wrap.await t with
  | .ok rr => return (ri, rr)
  | .error e => throw e

/-- The secured connection of an engine result, or a failed run. -/
private def securedOf (where_ : String) :
    Except _root_.Tls.Error _root_.Tls.Secured → Async _root_.Tls.Secured
  | .ok sc => return sc
  | .error e => throw <| IO.userError s!"{where_}: {e}"

/-- True when the engine join answers an orderly end. -/
private def engineJoinsOk (sc : _root_.Tls.Secured) : Async Bool := do
  return (← sc.join) matches .ok ()

/-- Run both handshakes: the responder as a task, the initiator here.
The await joins the task (§4.1, rule 2). -/
private def both (pI pR : SecurityProtocol) (c s : Connection) :
    Async (Except Libp2p.Core.Error SecureConn × Except Libp2p.Core.Error SecureConn) := do
  let t ← (Conc.Wrap.spawn (pR.handshake .responder s .empty).run :
    BaseIO (Task (Except IO.Error (Except Libp2p.Core.Error SecureConn))))
  let ri ← (pI.handshake .initiator c .empty).run
  match ← Conc.Wrap.await t with
  | .ok rr => return (ri, rr)
  | .error e => throw e

/-- Read until `n` bytes have arrived, or the end, from a secure
connection. -/
private def readN (sc : SecureConn) (n : Nat) : Async ByteArray :=
  readConn sc.toConnection n

/-- The secure connection of a result, or a failed run. -/
private def secured (where_ : String) : Except Libp2p.Core.Error SecureConn → Async SecureConn
  | .ok sc => return sc
  | .error e => throw <| IO.userError s!"{where_}: {e}"

/-- True when the join answers an orderly end. -/
private def joinsOk (sc : SecureConn) : Async Bool := do
  return (← sc.join.run) matches .ok ()

private def roundTrip (r : Runner) (split : Bool) : Async Unit := do
  let name := s!"tls sim{if split then " (split writes)" else ""}"
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  let (c, s) ← pair split
  let (ri, rr) ← both (Tls.securityProtocol cfgI) (Tls.securityProtocol cfgR) c s
  let ci ← secured name ri
  let cr ← secured name rr
  r.check s!"{name}: the initiator proves the responder's peer id" (ci.remotePeer == cfgR.localPeer)
  r.check s!"{name}: the responder proves the initiator's peer id" (cr.remotePeer == cfgI.localPeer)
  r.check s!"{name}: each side names its own peer id"
    (ci.localPeer == cfgI.localPeer && cr.localPeer == cfgR.localPeer)
  r.check s!"{name}: the handshake leaves no leftover" (ci.leftover.isEmpty && cr.leftover.isEmpty)
  ci.write "hello".toUTF8
  r.check s!"{name}: the responder reads the initiator's bytes" ((← readN cr 5) == "hello".toUTF8)
  cr.write "world!".toUTF8
  r.check s!"{name}: the initiator reads the responder's bytes" ((← readN ci 6) == "world!".toUTF8)
  -- Past one record: 300000 bytes take 19 records of 16 KiB.
  let big : ByteArray := ⟨(Array.range 300000).map fun k => UInt8.ofNat (k % 251)⟩
  -- The sim pipe holds a few chunks, so the write runs as a task while
  -- this task reads. The await joins it (§4.1, rule 2).
  let writer ← (Conc.Wrap.spawn (ci.write big) : BaseIO (Task (Except IO.Error Unit)))
  let got ← readN cr big.size
  discard <| Conc.Wrap.await writer
  r.check s!"{name}: a write of 19 records arrives whole" (got == big)
  ci.close
  r.check s!"{name}: after the close the peer reads the end" ((← cr.read).isNone)
  cr.close
  r.check s!"{name}: both joins answer an orderly end" ((← joinsOk ci) && (← joinsOk cr))

/-- The test value (§3.1): two runs from the same keys and clock prove
the same peer ids, and the certificate key is the fixed one. -/
private def fixedValue (r : Runner) : Async Unit := do
  let run : Async (Option (PeerId × PeerId)) := do
    let pI ← expectOk "fixed value" (← Tls.fixedKeyProtocol (← ed25519Key 5) (← fixedCertKey) vectorNow)
    let pR ← expectOk "fixed value" (← Tls.fixedKeyProtocol (← ed25519Key 6) (← fixedCertKey) vectorNow)
    let (c, s) ← pair
    match ← both pI pR c s with
    | (.ok ci, .ok cr) =>
      ci.close
      cr.close
      discard ci.join.run
      discard cr.join.run
      return some (ci.remotePeer, cr.remotePeer)
    | _ => return none
  let first ← run
  let second ← run
  let wantR ← expectOk "peer id" ((← ed25519Key 6).toPublic.bind PeerId.ofPubKey)
  let wantI ← expectOk "peer id" ((← ed25519Key 5).toPublic.bind PeerId.ofPubKey)
  r.check "tls fixed value: the handshake proves both fixed peer ids"
    (first == some (wantR, wantI))
  r.check "tls fixed value: a second run proves the same peer ids" (second == first)
  let cfg ← cfgOf 5
  r.check "tls fixed value: the configuration keeps the fixed certificate key"
    (cfg.identity.certificateKey == (← fixedCertKey))

/-- The responder's certificate was issued 200 years back, so its 100
years ended. The initiator refuses it inside the handshake, before it
sends its own certificate, so the responder gets the alert
`bad_certificate`. -/
private def expired (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4 (-6311520000)
  let (c, s) ← pair
  let (ri, rr) ← both (Tls.securityProtocol cfgI) (Tls.securityProtocol cfgR) c s
  r.check "tls sim expired: the initiator refuses an expired certificate"
    (match ri with
      | .error (.authentication d) => mentions d "expired"
      | _ => false)
  r.check "tls sim expired: the responder gets the alert bad_certificate"
    (gotAlert rr)

/-- The initiator's wall clock fails after the setup: the validity
window cannot be checked, so the initiator refuses the peer and closes
the connection (`Libp2p/Security/Tls/Protocol.lean`, "The time"). -/
private def clockFails (r : Runner) : Async Unit := do
  let cfgI := { (← cfgOf 3) with now := throw (IO.userError "no clock") }
  let cfgR ← cfgOf 4
  let (c, s) ← pair
  let (ri, rr) ← both (Tls.securityProtocol cfgI) (Tls.securityProtocol cfgR) c s
  r.check "tls sim clock fails: the initiator refuses the peer"
    (match ri with
      | .error (.authentication d) => mentions d "wall clock"
      | _ => false)
  -- The initiator refuses before the first byte of the handshake, so
  -- the responder's handshake reads the end of the connection.
  r.check "tls sim clock fails: the responder's handshake reads the close"
    (rr matches .error (.closed _))

/-- A client whose certificate lacks the extension: the server's check
refuses it, and the client's first read ends. The certificate is valid
at the server's fixed time, so the extension is the only rule it
breaks. -/
private def noExtension (r : Runner) : Async Unit := do
  let cfgR ← cfgOf 4
  let certKey ← fixedCertKey
  let cert ← expectOk "issue" (← (Crypto.issue certKey "1.3.6.1.4.1.53594.1.2" (fill 4 0) false
    (vectorNow - 60) (vectorNow + 3600)).run)
  let ctx ← expectOk "context" (← _root_.Tls.Context.new cert certKey Tls.alpn)
  let (c, s) ← pair
  let t ← (Conc.Wrap.spawn ((Tls.securityProtocol cfgR).handshake .responder s .empty).run :
    BaseIO (Task (Except IO.Error (Except Libp2p.Core.Error SecureConn))))
  let client ← _root_.Tls.handshake ctx false c .empty acceptAny
  let rr ← Conc.Wrap.await t
  r.check "tls sim no extension: the server refuses the client certificate for its extension"
    (match rr with
      | .ok (.error (.authentication d)) => mentions d "lacks the libp2p extension"
      | _ => false)
  -- The client finishes before the server checks its certificate (the
  -- spec's "Note for clients"), so its engine answers `.ok`; the
  -- server's alert then fails the client's first read.
  match client with
  | .ok sec =>
    r.check "tls sim no extension: the client's read ends" ((← sec.connection.read).isNone)
    sec.connection.close
    r.check "tls sim no extension: the client got the alert bad_certificate"
      (match ← sec.join with
        | .error e => mentions (toString e) badCertificateText
        | .ok () => false)
  | .error e => r.check s!"tls sim no extension: the client's engine finishes ({e})" false

/-- A client that offers another ALPN name: the server's engine refuses
the handshake. -/
private def wrongAlpn (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  let ctx ← expectOk "context"
    (← _root_.Tls.Context.new cfgI.identity.certificate cfgI.identity.certificateKey "other")
  let (c, s) ← pair
  let t ← (Conc.Wrap.spawn ((Tls.securityProtocol cfgR).handshake .responder s .empty).run :
    BaseIO (Task (Except IO.Error (Except Libp2p.Core.Error SecureConn))))
  let client ← _root_.Tls.handshake ctx false c .empty acceptAny
  let rr ← Conc.Wrap.await t
  r.check "tls sim wrong alpn: the server refuses the handshake"
    (rr matches .ok (.error (.protocol _)))
  r.check "tls sim wrong alpn: the client's handshake fails"
    (client matches .error (.handshake _))

/-- A server that sends a chain of two certificates: the client's
engine refuses it ("Endpoints MUST abort the connection attempt if
more than one certificate is received"). -/
private def chainOfTwo (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  let added ← (TlsNative.addChainCertificate cfgR.context.native cfgI.identity.certificate : IO Bool)
  r.check "tls sim chain of two: the context takes the extra certificate" added
  let (c, s) ← pair
  let (ri, rr) ← both (Tls.securityProtocol cfgI) (Tls.securityProtocol cfgR) c s
  r.check "tls sim chain of two: the client refuses a chain of two certificates"
    (match ri with
      | .error (.authentication d) => mentions d "sent 2 certificates"
      | _ => false)
  -- The client's engine sends its alert before it closes, and the
  -- server's engine fails on the alert.
  r.check "tls sim chain of two: the server gets the alert bad_certificate" (gotAlert rr)

/-! ## The records and the close -/

/-- A KeyUpdate (RFC 8446 §4.6.3) from the initiator asks the responder
to update its keys too. libssl answers "prior to sending its next
Application Data record" (the RFC), from its next write
(`Tls/Conn.lean`, "The order of the records"). So the responder's read
writes nothing, its next write carries one record more than the write
after it, and data flows both ways under the new keys. -/
private def keyUpdate (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  let (c, s) ← pair
  -- The size of each write on the responder's connection, newest first.
  let sizesR : OnceRef (List Nat) ← OnceRef.new []
  let recorded : Connection := { s with
    write := fun b => do sizesR.update (b.size :: ·); s.write b }
  let (ri, rr) ← engineBoth cfgI cfgR c recorded
  let ci ← securedOf "key update" ri
  let cr ← securedOf "key update" rr
  ci.keyUpdate
  ci.connection.write "x".toUTF8
  let before := (← (sizesR.get : BaseIO (List Nat))).length
  r.check "tls key update: the responder reads after the key update"
    ((← readConn cr.connection 1) == "x".toUTF8)
  let afterRead := (← (sizesR.get : BaseIO (List Nat))).length
  r.check s!"tls key update: the responder's read writes nothing ({before} then {afterRead} writes)"
    (afterRead == before)
  cr.connection.write "y".toUTF8
  cr.connection.write "z".toUTF8
  r.check "tls key update: the initiator reads under the responder's new keys"
    ((← readConn ci.connection 2) == "yz".toUTF8)
  -- The write of "y" also carries the responder's own KeyUpdate: one
  -- record of 27 bytes, the 5-byte record header, the 4-byte handshake
  -- header, the 1-byte `request_update`, the content type byte, and the
  -- 16-byte AEAD tag of every TLS 1.3 cipher suite (RFC 8446 §5.2).
  match ← (sizesR.get : BaseIO (List Nat)) with
  | z :: y :: _ =>
    r.check s!"tls key update: the responder's next write carries its KeyUpdate ({y} then {z} bytes)"
      (y == z + 27)
  | _ => r.check "tls key update: the responder wrote twice" false
  ci.connection.close
  cr.connection.close
  r.check "tls key update: both joins answer an orderly end"
    ((← engineJoinsOk ci) && (← engineJoinsOk cr))

/-- A record that fails to decrypt is a failed record, and the reader
sends the fatal alert libssl queued for it (`Tls/Conn.lean`,
"Failures"). The test writes a whole record of junk to the initiator's
connection under TLS. -/
private def failedRecord (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  let (c, s) ← pair
  let writesR ← OnceRef.new 0
  let (ri, rr) ← engineBoth cfgI cfgR c (counting s writesR)
  let ci ← securedOf "failed record" ri
  let cr ← securedOf "failed record" rr
  let before ← (writesR.get : BaseIO Nat)
  -- An application data record (type 23, legacy version 3.3) of 17
  -- bytes: the length of an empty plaintext, its content type, and the
  -- 16-byte tag. The bytes are not a valid ciphertext.
  c.write (⟨#[0x17, 0x03, 0x03, 0x00, 0x11]⟩ ++ ⟨Array.replicate 17 0⟩)
  r.check "tls failed record: the read ends" ((← cr.connection.read).isNone)
  r.check s!"tls failed record: the reader sends its alert ({before} then {← (writesR.get : BaseIO Nat)} writes)"
    ((← (writesR.get : BaseIO Nat)) == before + 1)
  cr.connection.close
  r.check "tls failed record: the join answers the failed record"
    ((← cr.join) matches .error (.record _))
  -- The initiator reads the alert as a TLS alert: `bad_record_mac`.
  r.check "tls failed record: the peer's read ends" ((← ci.connection.read).isNone)
  ci.connection.close
  r.check "tls failed record: the peer got the alert bad_record_mac"
    (match ← ci.join with
      | .error e => mentions (toString e) "alert bad record mac"
      | .ok () => false)

/-- `close` sends `close_notify`; `abort` sends nothing; a close while
a write is in flight sends nothing (Go's `Close`). -/
private def closeAlerts (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  -- `close`: one more write after the close, the alert. An encrypted
  -- alert record is 24 bytes: the 5-byte record header, the 2-byte
  -- alert, the content type byte, and the 16-byte AEAD tag.
  let (c, s) ← pair
  let sizesI : OnceRef (List Nat) ← OnceRef.new []
  let recorded : Connection := { c with
    write := fun b => do sizesI.update (b.size :: ·); c.write b }
  let (ri, rr) ← engineBoth cfgI cfgR recorded s
  let ci ← securedOf "close" ri
  let cr ← securedOf "close" rr
  let before := (← (sizesI.get : BaseIO (List Nat))).length
  ci.connection.close
  discard ci.join
  let sizes ← (sizesI.get : BaseIO (List Nat))
  r.check s!"tls close: the close writes one alert record ({sizes.head?} bytes)"
    (sizes.length == before + 1 && sizes.head? == some 24)
  r.check "tls close: the peer reads the end" ((← cr.connection.read).isNone)
  cr.connection.close
  r.check "tls close: the peer's join answers an orderly end" (← engineJoinsOk cr)
  -- `abort`: no write after it.
  let (c, s) ← pair
  let writesI ← OnceRef.new 0
  let (ri, rr) ← engineBoth cfgI cfgR (counting c writesI) s
  let ci ← securedOf "abort" ri
  let cr ← securedOf "abort" rr
  let before ← (writesI.get : BaseIO Nat)
  ci.abort
  discard ci.join
  r.check "tls abort: the abort writes nothing" ((← (writesI.get : BaseIO Nat)) == before)
  r.check "tls abort: the peer reads the end" ((← cr.connection.read).isNone)
  cr.connection.close
  discard cr.join
  -- A close during a write that a peer that never reads parks. The sim
  -- pipe holds `simPipeChunks` chunks, one per connection write, so
  -- write number `simPipeChunks + 1` after the handshake parks.
  let (c, s) ← pair
  let writesI : OnceRef Nat ← OnceRef.new 0
  -- The count of the write that parks, set after the handshake.
  let parking : OnceRef Nat ← OnceRef.new 0
  let parked : Chan Unit ← Chan.new 1
  let watched : Connection := { c with
    write := fun b => do
      let n ← (writesI.updateGet fun k => (k + 1, k + 1) : BaseIO Nat)
      if n == (← (parking.get : BaseIO Nat)) then
        discard <| (parked.trySend () : BaseIO Bool)
      c.write b }
  let (ri, rr) ← engineBoth cfgI cfgR watched s
  let ci ← securedOf "close in flight" ri
  let cr ← securedOf "close in flight" rr
  let before ← (writesI.get : BaseIO Nat)
  parking.set (before + Streams.simPipeChunks + 1)
  let writer ← (Conc.Wrap.spawn (do
      for _ in List.range (Streams.simPipeChunks + 1) do
        ci.connection.write "x".toUTF8) : BaseIO (Task (Except IO.Error Unit)))
  -- Park: the start of the write that parks wakes it.
  discard <| parked.recv
  let atClose ← (writesI.get : BaseIO Nat)
  ci.connection.close
  discard ci.join
  let w ← Conc.Wrap.await writer
  r.check s!"tls close in flight: the close writes no alert ({atClose} then {← (writesI.get : BaseIO Nat)} writes)"
    ((← (writesI.get : BaseIO Nat)) == atClose)
  let wText := match w with | .ok () => "it returned" | .error e => s!"it threw {e}"
  r.check s!"tls close in flight: the parked write fails ({wText})" (w matches .error _)
  cr.abort
  discard cr.join

/-- The end of the connection, by Go's rule (`Tls/Conn.lean`,
"Failures"): at a record boundary, an orderly end with no
`close_notify`; inside a record, a failed record. The tests write to
the initiator's connection under TLS. -/
private def connectionEnd (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  let (c, s) ← pair
  let (ri, rr) ← engineBoth cfgI cfgR c s
  let ci ← securedOf "end" ri
  let cr ← securedOf "end" rr
  c.close
  r.check "tls end: an end at a record boundary reads as the end" ((← cr.connection.read).isNone)
  cr.connection.close
  r.check "tls end: an end at a record boundary is an orderly end" (← engineJoinsOk cr)
  ci.abort
  discard ci.join
  let (c, s) ← pair
  let (ri, rr) ← engineBoth cfgI cfgR c s
  let ci ← securedOf "cut" ri
  let cr ← securedOf "cut" rr
  -- Three bytes of a five-byte record header.
  c.write ⟨#[0x17, 0x03, 0x03]⟩
  c.close
  r.check "tls end: an end inside a record reads as the end" ((← cr.connection.read).isNone)
  cr.connection.close
  r.check "tls end: an end inside a record is a failed record"
    (match ← cr.join with
      | .error (.record d) => mentions d "inside a TLS record"
      | _ => false)
  ci.abort
  discard ci.join

/-! ## The upgrade -/

/-- Both upgrades with `/tls/1.0.0` and yamux, the initiator here. -/
private def upgradeBoth (cfgI cfgR : Tls.Config) (expected : Option PeerId) (c s : Connection) :
    Async (Except Libp2p.Core.Error (MuxSession × PeerId) × Except Libp2p.Core.Error (MuxSession × PeerId)) := do
  let t ← (Conc.Wrap.spawn
      (Libp2p.Negotiate.upgrade .responder s .empty none [Tls.securityProtocol cfgR]
        [Libp2p.Mux.yamux]).run :
    BaseIO (Task (Except IO.Error (Except Libp2p.Core.Error (MuxSession × PeerId)))))
  let ri ← (Libp2p.Negotiate.upgrade .initiator c .empty expected [Tls.securityProtocol cfgI]
    [Libp2p.Mux.yamux]).run
  match ← Conc.Wrap.await t with
  | .ok rr => return (ri, rr)
  | .error e => throw e

private def upgrade (r : Runner) : Async Unit := do
  let cfgI ← cfgOf 3
  let cfgR ← cfgOf 4
  let (c, s) ← pair
  match ← upgradeBoth cfgI cfgR (some cfgR.localPeer) c s with
  | (.ok (si, pr), .ok (sr, pi)) =>
    r.check "tls upgrade: both sides prove the other's peer id"
      (pr == cfgR.localPeer && pi == cfgI.localPeer)
    let st ← match ← (si.openStream ⟨"/test/echo"⟩).run with
      | .ok st => pure st
      | .error e => throw <| IO.userError s!"open: {e}"
    r.check "tls upgrade: the stream write succeeds" ((← st.write "ping".toUTF8) matches .ok _)
    let some sr' ← sr.accept | throw <| IO.userError "accept"
    r.check "tls upgrade: a yamux stream carries bytes over TLS"
      (match ← sr'.read with | .ok (some b) => b == "ping".toUTF8 | _ => false)
    si.close
    sr.close
    discard si.join.run
    discard sr.join.run
  | _ => r.check "tls upgrade: both upgrades succeed" false
  -- An unexpected peer: the initiator expects another id.
  let (c, s) ← pair
  let wrong ← expectOk "peer id" ((← ed25519Key 9).toPublic.bind PeerId.ofPubKey)
  match ← upgradeBoth cfgI cfgR (some wrong) c s with
  | (ri, rr) =>
    r.check "tls upgrade: an unexpected peer id fails the upgrade"
      (ri matches .error (.authentication _))
    if let .ok (sr, _) := rr then
      sr.close
      discard sr.join.run

/-- The suite. -/
def run (r : Runner) : IO Unit := do
  r.section "libp2p TLS (W5.11)" "libp2p/specs tls/tls.md; vendor/go-libp2p/p2p/security/tls"
  vectors r
  extensionRules r
  codec r
  issued r
  Async.run do
    roundTrip r false
    roundTrip r true
    fixedValue r
    expired r
    clockFails r
    noExtension r
    wrongAlpn r
    keyUpdate r
    failedRecord r
    closeAlerts r
    connectionEnd r
    chainOfTwo r
    upgrade r

end Tests.TlsSuite
