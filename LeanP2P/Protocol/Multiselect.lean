import LeanP2P.Conn.Reader
import LeanP2P.Net.Varint
import LeanP2P.Crypto.Bytes
/-!
# Multistream-select 1.0.0 (VECTOR_TEST_PLAN.md, phase 3 step 15)

Per multiformats/multistream-select: every message is
`<uvarint length><payload>` where the payload is UTF-8 text INCLUDING a
trailing `\n` (the length counts the `\n`). Messages are capped at 1024
bytes, matching go-multistream's `lpReadBuf`.

- pure codec: `msgBytes` / `decodeMsg?` (self-delimiting, length-checked),
  the `ls` reply framing (`lsPayload` / `decodeLsPayload?`), and the
  negotiation core `choose` (proven).
- IO shell: a buffered reader over any `Connection` (chunk boundaries from
  the transport never matter - writes may be split or coalesced),
  listener (`selectResponder`, handles `ls` and coalesced header +
  proposal), naive dialer (`selectInitiator`) and the go-compatible lazy
  dialer (`selectInitiatorLazy`: header and proposal in one write,
  verified on first use - `V1Lazy` in go-multistream).

Spec wire examples (multistream-select README):
- `na`      -> 0x03 6e 61 0a
- `ls`      -> 0x03 6c 73 0a
- header    -> 0x13 "/multistream/1.0.0\n"
- ls reply  -> one message whose body is
  `<varint(len+1)><proto>\n` per protocol, terminated by a final `\n`
-/

namespace LeanP2P.Multiselect

/-! ## Negotiation core (proven) -/

/-- Pure negotiation core (first of `ours` that `theirs` also supports). -/
def choose (ours theirs : List String) : Option String :=
  List.find? theirs.contains ours

theorem choose_spec {ours theirs : List String} {p : String} (h : choose ours theirs = some p) :
    p ∈ ours ∧ theirs.contains p = true := by
  rw [choose] at h
  exact ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-! ## Message framing (pure) -/

def header : String := "/multistream/1.0.0"

/-- Maximum message length in bytes (go-multistream `lpReadBuf`). -/
def maxMsg : Nat := 1024

/-- Message bytes: uvarint length of `msg ++ "\n"` (including the newline),
followed by the payload bytes. -/
def msgBytes (m : String) : List Nat :=
  let payload := Bytes.toNatList (Bytes.ofString (m ++ "\n"))
  Varint.encode payload.length ++ payload

/-- Decode one message from a buffer. Returns the message and the total
number of bytes consumed (which may be less than the buffer size when the
transport coalesced a following message). `none` when more bytes are
needed (`size` marker) or the encoding is invalid. -/
inductive MsgDecode where
  /-- need at least this many more bytes -/
  | more (need : Nat)
  /-- protocol error (too large, no trailing newline, bad UTF-8) -/
  | bad
  /-- message, bytes consumed -/
  | done (msg : String) (consumed : Nat)

def decodeMsg? : ByteArray → MsgDecode
  | bs =>
    match Varint.decodeB? bs 0 with
    | none =>
        -- a varint that could not decode with ≥ 9 bytes available can
        -- never complete (the uvarint spec caps varints at 9 bytes) or
        -- is non-minimal: protocol error, not "need more bytes" - the
        -- reader must not accumulate forever on a hostile length
        if bs.size ≥ 9 then .bad else .more 1
    | some (len, varintLen) =>
      if len > maxMsg then .bad
      else if bs.size < varintLen + len then .more (varintLen + len - bs.size)
      else
        -- the payload includes the trailing `\n` (its length counts it)
        let payload := bs.extract varintLen (varintLen + len)
        let last := payload.toList.getLast?
        if len = 0 ∨ last != some 10 then .bad
        else
          let body := payload.extract 0 (len - 1)
          match Bytes.toString? body with
          | none => .bad
          | some s => .done s (varintLen + len)

/-! ## `ls` reply framing (pure) -/

/-- The body of an `ls` reply: `<varint(len+1)><proto>\n` per protocol,
terminated by a final `\n`. -/
def lsPayload (protos : List String) : List Nat :=
  (protos.flatMap fun p =>
    let b := Bytes.toNatList (Bytes.ofString (p ++ "\n"))
    Varint.encode b.length ++ b) ++ [10]

/-- Decode an `ls` reply body into the protocol list (rust-libp2p
`Message::Protocols` semantics: repeated length-prefixed names ending with
a bare `\n`); fuel bounds the recursion. -/
def decodeLsPayloadF : Nat → List Nat → List String → Option (List String)
  | 0, _, _ => none
  | _ + 1, [10], acc => some acc.reverse
  | _ + 1, [], _ => none
  | fuel + 1, bs, acc =>
      match Varint.decode? bs with
      | none => none
      | some (len, rest) =>
        if len = 0 ∨ rest.length < len then none
        else if rest.getLast? != some 10 then none
        else
          match Bytes.toString? (Bytes.ofNatList (rest.take (len - 1))) with
          | none => none
          | some p => decodeLsPayloadF fuel (rest.drop len) (p :: acc)

def decodeLsPayload? (bs : List Nat) : Option (List String) :=
  decodeLsPayloadF bs.length bs []

/-! ## IO shell -/

def writeMsg (c : Connection) (m : String) : IO Unit :=
  c.write (Bytes.ofNatList (msgBytes m))

def writeRaw (c : Connection) (bs : List Nat) : IO Unit :=
  c.write (Bytes.ofNatList bs)

/-- Read one message through a buffered reader; coalesced or split
transports both work (leftover bytes stay in the reader). -/
partial def readMsg (r : BufReader) : IO (Option String) := do
  -- take the buffered bytes out first (they must not be read twice)
  let first ← r.buf.get
  r.buf.set ByteArray.empty
  let rec go (acc : ByteArray) : IO (Option String) := do
    match decodeMsg? acc with
    | .bad => return none
    | .done s c => do
      -- keep any coalesced bytes for the next message
      r.buf.set (acc.extract c acc.size)
      return (some s)
    | .more _need => do
      let chunk ← r.readAvail
      match chunk with
      | none => return none
      | some b => go (acc ++ b)
  go first

/-- Listener side: echo the header once, then answer proposals until one is
selected (or the stream ends). `ls` lists the supported protocols. A
re-sent header (the libp2p upgrader retries its next candidate after a
`na`) is echoed again so both sides stay in sync. -/
partial def selectResponder (r : BufReader) (c : Connection)
    (supported : List String) : IO (Option String) := do
  match ← readMsg r with
  | none => return none
  | some h =>
    if h != header then
      writeMsg c "na"
      return none
    else
      writeMsg c header
      go r c supported
where
  go (r : BufReader) (c : Connection) (supported : List String) :
      IO (Option String) := do
    match ← readMsg r with
    | none => return none
    | some "ls" =>
      let body := lsPayload supported
      writeRaw c (Varint.encode body.length ++ body)
      go r c supported
    | some proto =>
      if proto == header then
        writeMsg c header
        go r c supported
      else if supported.contains proto then
        writeMsg c proto
        return (some proto)
      else
        writeMsg c "na"
        go r c supported

/-- Dialer side: header exchange, then propose `proto`. -/
def selectInitiator (r : BufReader) (c : Connection) (proto : String) :
    IO (Option String) := do
  writeMsg c header
  match ← readMsg r with
  | none => return none
  | some h =>
    if h != header then return none
    else
      writeMsg c proto
      match ← readMsg r with
      | none => return none
      | some p => return (if p = proto then some p else none)

/-- Lazy dialer (go-multistream `NewMSSelect`): the multistream header and
the proposal are written back-to-back in a single shot without waiting for
a response; the negotiation is only verified when the first response
arrives. -/
def selectInitiatorLazy (r : BufReader) (c : Connection) (proto : String) :
    IO (Option String) := do
  writeRaw c (msgBytes header ++ msgBytes proto)
  match ← readMsg r with
  | none => return none
  | some h =>
    if h != header then return none
    match ← readMsg r with
    | none => return none
    | some p => return (if p = proto then some p else none)

/-- Ask the peer to list its protocols (`ls`), read the reply. -/
def listProtocols (r : BufReader) (c : Connection) : IO (Option (List String)) := do
  writeMsg c header
  match ← readMsg r with
  | none => return none
  | some h =>
    if h != header then return none
    writeMsg c "ls"
    match ← readMsg r with
    | none => return none
    | some body =>
      return decodeLsPayload? (Bytes.toNatList (Bytes.ofString (body ++ "\n")))

end LeanP2P.Multiselect
