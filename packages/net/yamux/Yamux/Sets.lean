import Bytes

/-!
# The closed sets of yamux

The yamux spec enumerates three small sets (`vendor/specs/yamux`,
"Framing"), and each one becomes a closed set here (ARCHITECTURE §3.4):

| Set | Field | Members |
|---|---|---|
| `FrameType` | type, 8 bits | `0x0` data, `0x1` window update, `0x2` ping, `0x3` go away |
| `GoAwayCode` | length of a go-away frame | `0x0` normal, `0x1` protocol error, `0x2` internal error |
| `Flags` | flags, 16 bits | `0x1` SYN, `0x2` ACK, `0x4` FIN, `0x8` RST |

Each enumeration carries `toCode`, `ofCode?`, and the theorem
`ofCode?ToCode`; `decide` or `rfl` closes it. The converse,
`toCodeOfCode?`, lets the header codec prove that a decode re-encodes
to its input.

`Flags` is a structure of four `Bool`s and the other twelve bits of the
field. The bit arithmetic happens once, in its `Codec` instance. The
spec defines four flags and says nothing of the other bits. go-yamux
reads the field raw and tests only the four (`vendor/go-yamux/const.go`,
lines 217 to 219), and rust-yamux keeps the raw `u16`
(`vendor/rust-yamux/yamux/src/frame/header.rs`, line 382), so a peer that sets another bit keeps
its session with both. `other` carries those bits through the codec, so
a decode re-encodes to its input, as the `LawfulCodec` law demands
(§3.2), and the core reads only the four flags.
-/

set_option autoImplicit false

namespace Yamux

open Bytes

/-! ## Frame type -/

/-- The type of a frame (spec, "Type Field"). -/
inductive FrameType where
  /-- `0x0`: data for a stream. -/
  | data
  /-- `0x1`: a window update for a stream. -/
  | windowUpdate
  /-- `0x2`: a ping, on the session. -/
  | ping
  /-- `0x3`: the end of the session. -/
  | goAway
  deriving DecidableEq, Repr, Hashable

namespace FrameType

/-- The wire code. -/
def toCode : FrameType → Nat
  | .data => 0
  | .windowUpdate => 1
  | .ping => 2
  | .goAway => 3

/-- The type of a wire code. `none` for a code the spec does not
define. -/
def ofCode? : Nat → Option FrameType
  | 0 => some .data
  | 1 => some .windowUpdate
  | 2 => some .ping
  | 3 => some .goAway
  | _ => none

/-- Every frame type reads back from its code: the conformance theorem
of the table (§3.4). -/
theorem ofCode?ToCode (t : FrameType) : ofCode? (toCode t) = some t := by
  cases t <;> rfl

/-- A code that reads as a frame type is that type's code, so the
decoder accepts no second spelling of a type. -/
theorem toCodeOfCode? {n : Nat} {t : FrameType} (h : ofCode? n = some t) : toCode t = n := by
  unfold ofCode? at h
  split at h <;> first | (cases h; rfl) | cases h

end FrameType

/-! ## Go-away code -/

/-- Why a session ends (spec, "Session termination"). -/
inductive GoAwayCode where
  /-- `0x0`: normal termination. -/
  | normal
  /-- `0x1`: the peer broke the protocol. -/
  | protocolError
  /-- `0x2`: the sender failed. -/
  | internalError
  deriving DecidableEq, Repr, Hashable

namespace GoAwayCode

/-- The wire code. -/
def toCode : GoAwayCode → Nat
  | .normal => 0
  | .protocolError => 1
  | .internalError => 2

/-- The code of a wire value. `none` for a value the spec does not
define. -/
def ofCode? : Nat → Option GoAwayCode
  | 0 => some .normal
  | 1 => some .protocolError
  | 2 => some .internalError
  | _ => none

/-- Every go-away code reads back from its number: the conformance
theorem of the table (§3.4). -/
theorem ofCode?ToCode (c : GoAwayCode) : ofCode? (toCode c) = some c := by
  cases c <;> rfl

/-- A number that reads as a go-away code is that code's number. -/
theorem toCodeOfCode? {n : Nat} {c : GoAwayCode} (h : ofCode? n = some c) : toCode c = n := by
  unfold ofCode? at h
  split at h <;> first | (cases h; rfl) | cases h

end GoAwayCode

/-! ## Flags -/

/-- The flags of a frame (spec, "Flag Field"). -/
structure Flags where
  /-- `0x1`: the start of a stream; on a ping, the request. -/
  syn : Bool
  /-- `0x2`: the acceptance of a stream; on a ping, the response. -/
  ack : Bool
  /-- `0x4`: the half-close of the sender's direction. -/
  fin : Bool
  /-- `0x8`: the reset of a stream. -/
  rst : Bool
  /-- The bits `0x10` to `0x8000`, which the spec does not define, as
  the field over 16. The field exists so that the codec stays a
  `LawfulCodec`: a decode must re-encode to its input, so the decoder
  keeps the bits instead of dropping them. Their content is ignored:
  the core never reads them, and we send 0. -/
  other : Fin 4096 := 0
  deriving DecidableEq, Repr, Hashable

namespace Flags

/-- No flag set. -/
def none : Flags := ⟨false, false, false, false, 0⟩

/-- The 16-bit field of the flags. -/
def toBits (f : Flags) : Nat :=
  (if f.syn then 1 else 0) + (if f.ack then 2 else 0) +
    (if f.fin then 4 else 0) + (if f.rst then 8 else 0) + f.other.val * 16

/-- The flags of a bit field. `none` for a value past 16 bits, which no
two bytes carry. -/
def ofBits? (n : Nat) : Option Flags :=
  if h : n < 65536 then
    some ⟨n % 2 = 1, n / 2 % 2 = 1, n / 4 % 2 = 1, n / 8 % 2 = 1, ⟨n / 16, by omega⟩⟩
  else .none

/-- The flags fit the 16-bit field of the header. -/
theorem toBitsLt (f : Flags) : f.toBits < 65536 := by
  obtain ⟨s, a, fi, r, o⟩ := f
  have ho := o.isLt
  simp only [toBits]
  split <;> split <;> split <;> split <;> omega

/-- A bit field below 16 bits reads back to itself. Each `split` cases
one flag, and `omega` closes the arithmetic of the division by powers
of two. -/
private theorem toBitsOfBitsLt (n : Nat) (hn : n < 65536) :
    toBits ⟨n % 2 = 1, n / 2 % 2 = 1, n / 4 % 2 = 1, n / 8 % 2 = 1, ⟨n / 16, by omega⟩⟩ = n := by
  simp only [toBits, decide_eq_true_eq]
  split <;> split <;> split <;> split <;> omega

/-- Flags read from a field write back to that field, the twelve
undefined bits included (`other`), so the codec is lawful. -/
theorem toBitsOfBits? {n : Nat} {f : Flags} (h : ofBits? n = some f) : f.toBits = n := by
  unfold ofBits? at h
  split at h
  · next hn =>
    cases h
    exact toBitsOfBitsLt n hn
  · cases h

/-- Flags read back from the field they write. -/
theorem ofBits?ToBits (f : Flags) : ofBits? f.toBits = some f := by
  obtain ⟨s, a, fi, r, o⟩ := f
  have ho := o.isLt
  have hlt := toBitsLt ⟨s, a, fi, r, o⟩
  unfold ofBits?
  simp only [hlt, ↓reduceDIte]
  -- Each case fixes the four flags; `omega` reads each bit back out of
  -- the sum, and the quotient by 16 is `other`.
  cases s <;> cases a <;> cases fi <;> cases r <;>
    simp only [toBits, Option.some.injEq, Flags.mk.injEq, Fin.ext_iff, Bool.false_eq_true,
      ↓reduceIte, decide_eq_true_eq, decide_eq_false_iff_not] <;> omega

/-- The flags field: 16 bits, big-endian. -/
def encode (f : Flags) : List Nat := [f.toBits / 256, f.toBits % 256]

/-- The flags field at the front of the input, and the rest. -/
def decode? (l : List Nat) : Except DecodeError (Flags × List Nat) :=
  match take? 2 l with
  | .error e => .error e
  | .ok ([hi, lo], rest) =>
    match ofBits? (hi * 256 + lo) with
    | some f => .ok (f, rest)
    | .none => .error .malformed
  -- `take? 2` answers two bytes, so this arm never runs.
  | .ok _ => .error .malformed

instance : Codec Flags where
  encode := encode
  decode? := decode?

instance : LawfulCodec Flags where
  decodeEncode f := by
    show decode? (encode f) = _
    have hb := toBitsLt f
    -- `take? 2` returns the two bytes whole; the field reads back as
    -- `toBits f`.
    have ht : take? 2 [f.toBits / 256, f.toBits % 256] =
        .ok ([f.toBits / 256, f.toBits % 256], []) := by
      simpa using take?Append (b := [f.toBits / 256, f.toBits % 256]) [] (by simp; omega)
    have hsum : f.toBits / 256 * 256 + f.toBits % 256 = f.toBits := by omega
    simp only [decode?, encode, ht, hsum, ofBits?ToBits]
  encodeDecode l f rest h := by
    show encode f ++ rest = l
    simp only [Codec.decode?, decode?] at h
    split at h
    · cases h
    · next hi lo r ht =>
      split at h
      · next f' hf =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hsplit, -, hbytes⟩ := ofTake? ht
        have hlo := hbytes lo (by simp)
        have hbits := toBitsOfBits? hf
        -- The field is `hi * 256 + lo` with `lo` a byte, so its high and
        -- low bytes are `hi` and `lo`.
        have hh : f'.toBits / 256 = hi := by omega
        have hl : f'.toBits % 256 = lo := by omega
        simp only [encode, hh, hl]
        simpa using hsplit
      · cases h
    · cases h

example : Codec.encode (⟨true, false, true, false, 0⟩ : Flags) = [0, 5] := rfl
/-- A bit the spec does not define passes through the codec. -/
example : decode? [0, 16, 9] = .ok (⟨false, false, false, false, 1⟩, [9]) := rfl
example : decode? [0] = .error .truncated := rfl

end Flags

end Yamux
