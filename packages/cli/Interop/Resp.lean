import Bytes
import Multiformats.Constants

/-!
# RESP2: the reply headers and the command form

The harness coordinates through Redis (the transport-interop test
plan, `vendor/test-plans/transport-interop/README.md`, "Dialer" and
"Listener"). Redis speaks RESP. The client sends each command as an
array of bulk strings, and the first byte of each reply names its type
(the RESP spec, "RESP protocol description"). The harness sends three
commands, `PING`, `RPUSH`, and `BLPOP`, and reads RESP2 replies only:

* `+` a simple string, such as `+PONG`
* `-` a simple error, which the client raises
* `:` a signed 64-bit integer, such as the list length of `RPUSH`
* `$` a bulk string, `$<length>` then the bytes and a CRLF, or the null
  bulk string `$-1`
* `*` an array, `*<count>` then its elements, or the null array `*-1`,
  which is the `BLPOP` answer at its timeout

This module is the pure part: the parse of one header line, and the
encoding of one command. Both work over the `List Nat` byte model
(CLAUDE.md, "Proofs and tests"). `Interop.Redis` reads the lines from
the connection and calls the parse.

## The caps

The server supplies every length, so each one has a cap that applies
before the read allocates (cli ARCHITECTURE, contract 6; PRINCIPLES
2.3). The largest value the harness reads is the listener's address,
as multiaddr text. The multiformats JSON path admits address text up to
`maxAddressJsonBytes`, and JSON escaping never shortens a string. So
that constant bounds every address text the harness can accept, and it
caps each reply line and each bulk string. The longest array the
harness reads is the `BLPOP` answer: the key and the value. A longer
array header is an error before any element is read.
-/

set_option autoImplicit false

namespace Interop.Resp

/-- The cap of one reply line and of one bulk string, in bytes: the
largest address text the multiformats JSON path admits (module doc,
"The caps"). -/
def maxReplyBytes : Nat := Multiformats.maxAddressJsonBytes

/-- The cap of one array reply: the key and the value of a `BLPOP`
answer. -/
def maxArrayLength : Nat := 2

/-- The byte of the CR that ends every RESP line, before the LF. -/
def cr : Nat := 13

/-- The byte of the LF that ends every RESP line. -/
def lf : Nat := 10

/-- Why a Redis exchange failed. -/
inductive Error where
  /-- A line or a bulk string over `maxReplyBytes`, or an array over
  `maxArrayLength`. -/
  | tooLong
  /-- Bytes that break RESP2. -/
  | malformed (detail : String)
  /-- The connection ended inside a reply. -/
  | closed
  /-- The server answered with a simple error. -/
  | server (message : String)
  /-- A well-formed reply of a type that the command does not give. -/
  | unexpected (detail : String)
  deriving Repr, DecidableEq

/-- The parsed first line of one reply. A bulk string and an array carry
their length, or `none` for the null forms. -/
inductive Header where
  /-- `+`: a simple string. -/
  | simple (text : String)
  /-- `-`: a simple error. -/
  | error (text : String)
  /-- `:`: an integer. -/
  | integer (value : Int)
  /-- `$`: a bulk string of this length, or the null bulk string. -/
  | bulk (length : Option Nat)
  /-- `*`: an array of this many elements, or the null array. -/
  | array (length : Option Nat)
  deriving Repr, DecidableEq

/-! ## Numbers -/

/-- True for the bytes of the ASCII digits `0` to `9`. -/
def isDigit (b : Nat) : Bool := 48 ≤ b && b ≤ 57

/-- The value of a decimal numeral: one or more ASCII digits, and
nothing else. -/
def digits? (l : List Nat) : Option Nat :=
  if l.isEmpty || !l.all isDigit then none
  else some (l.foldl (fun acc b => 10 * acc + (b - 48)) 0)

/-- The ASCII digits of `n` in base 10. -/
def decimal (n : Nat) : List Nat :=
  (Nat.toDigits 10 n).map Char.toNat

/-- A length field: a numeral up to `cap`, or `-1` for the null form.
A numeral over `cap` is `tooLong`, before any read takes the bytes it
announces. -/
def length? (l : List Nat) (cap : Nat) : Except Error (Option Nat) :=
  match l with
  | [45, 49] => .ok none
  | _ =>
    match digits? l with
    | none => .error (.malformed "a length that is not a numeral")
    | some n => if n ≤ cap then .ok (some n) else .error .tooLong

/-- An integer reply: an optional `+` or `-`, then a numeral (the RESP
spec, "Integers"). -/
def integer? (l : List Nat) : Except Error Int :=
  let (sign, rest) : Int × List Nat := match l with
    | 45 :: rest => (-1, rest)
    | 43 :: rest => (1, rest)
    | rest => (1, rest)
  match digits? rest with
  | some n => .ok (sign * n)
  | none => .error (.malformed "an integer that is not a numeral")

/-! ## Headers -/

/-- The text of a simple string or a simple error. The spec forbids a CR
and an LF inside it, and the line reader splits at the first CRLF, so
only the UTF-8 check is left. -/
def text? (l : List Nat) : Except Error String :=
  match Bytes.toString? (Bytes.ofNatList l) with
  | some s => .ok s
  | none => .error (.malformed "a simple string that is not UTF-8")

/-- The header of one reply, from its first line without the CRLF. -/
def parseHeader : List Nat → Except Error Header
  | 43 :: rest => .simple <$> text? rest
  | 45 :: rest => .error <$> text? rest
  | 58 :: rest => .integer <$> integer? rest
  | 36 :: rest => .bulk <$> length? rest maxReplyBytes
  | 42 :: rest => .array <$> length? rest maxArrayLength
  | _ => .error (.malformed "an unknown type byte")

/-! ## Commands -/

/-- One bulk string: `$`, the length, CRLF, the bytes, CRLF. -/
def encodeBulk (b : List Nat) : List Nat :=
  36 :: decimal b.length ++ [cr, lf] ++ b ++ [cr, lf]

/-- One command: an array of bulk strings, the name first (the RESP
spec, "Sending commands to a Redis server"). -/
def encodeCommand (args : List (List Nat)) : List Nat :=
  42 :: decimal args.length ++ [cr, lf] ++ args.flatMap encodeBulk

/-! ## Theorems -/

/-- A length field over its cap is `tooLong`, so no read takes the
bytes it announces. -/
theorem length?OverCap {l : List Nat} {n cap : Nat} (h : digits? l = some n) (hc : cap < n) :
    length? l cap = .error .tooLong := by
  unfold length?
  split
  · -- `-1` is no numeral, so `h` cannot hold here.
    simp [digits?, isDigit] at h
  · simp only [h, show ¬n ≤ cap from by omega, ↓reduceIte]

/-- A bulk string header over `maxReplyBytes` is `tooLong`. -/
theorem parseHeaderBulkOverCap {l : List Nat} {n : Nat} (h : digits? l = some n)
    (hc : maxReplyBytes < n) : parseHeader (36 :: l) = .error .tooLong := by
  simp only [parseHeader, length?OverCap h hc]
  rfl

/-- An array header over `maxArrayLength` is `tooLong`. -/
theorem parseHeaderArrayOverCap {l : List Nat} {n : Nat} (h : digits? l = some n)
    (hc : maxArrayLength < n) : parseHeader (42 :: l) = .error .tooLong := by
  simp only [parseHeader, length?OverCap h hc]
  rfl

example : parseHeader [36, 45, 49] = .ok (.bulk none) := rfl
example : parseHeader [42, 51] = .error .tooLong := rfl
example : encodeCommand [[80, 73, 78, 71]] = [42, 49, 13, 10, 36, 52, 13, 10, 80, 73, 78, 71, 13, 10] :=
  rfl
-- The UTF-8 check of `text?` runs compiled code that the kernel does not
-- reduce well, so this case runs at build time instead.
#guard parseHeader [43, 80, 79, 78, 71] matches .ok (.simple "PONG")

end Interop.Resp
