import Bytes
import Yamux.Constants

/-!
# Yamux closed sets

The sets the yamux specification enumerates, as closed inductives
(ARCHITECTURE §3.4): the frame type, the `GoAway` reason code, and the
flags.

Each set carries `toCode` and `ofCode?` with the conformance theorem
`ofCode? (toCode t) = some t`. The theorem is the proof that the table
is total on its own image, and `decide` closes it because the sets are
finite.

Flags are a structure of four `Bool`s, not an inductive, because the
four bits are independent: a single frame carries any combination. The
bit arithmetic happens once, in the `Bytes.Codec` instance below, and
every other module reads the `Bool` fields.
-/

namespace Yamux

/-! ## The frame type -/

/-- The four frame types of the yamux specification. -/
inductive FrameType where
  /-- A data frame: the payload is application bytes. -/
  | data
  /-- A window update: the length field carries the credit delta. -/
  | windowUpdate
  /-- A ping: the length field carries the opaque value to echo. -/
  | ping
  /-- A session teardown: the length field carries a `GoAwayCode`. -/
  | goAway
  deriving Repr, DecidableEq, BEq, Hashable

namespace FrameType

/-- The wire code of a frame type. -/
def toCode : FrameType → Nat
  | .data => 0
  | .windowUpdate => 1
  | .ping => 2
  | .goAway => 3

/-- The frame type a wire code names, if it names one. -/
def ofCode? : Nat → Option FrameType
  | 0 => some .data
  | 1 => some .windowUpdate
  | 2 => some .ping
  | 3 => some .goAway
  | _ => none

/-- A code that names a frame type is that type's code. The proof splits
the four constructors and the five shapes of the code. -/
theorem eq_toCode_of_ofCode?_eq_some {n : Nat} {t : FrameType}
    (h : ofCode? n = some t) : n = toCode t := by
  cases t <;>
    (cases n with
     | zero => simp_all [ofCode?, toCode]
     | succ n1 => cases n1 with
       | zero => simp_all [ofCode?, toCode]
       | succ n2 => cases n2 with
         | zero => simp_all [ofCode?, toCode]
         | succ n3 => cases n3 with
           | zero => simp_all [ofCode?, toCode]
           | succ n4 => simp [ofCode?] at h)

/-- Every frame type fits in one byte, so the codec needs no range check
on the type field. -/
theorem toCode_lt_four (t : FrameType) : toCode t < 4 := by
  cases t <;> decide

/-- The table round trip: every frame type decodes from its own code.
This is the conformance proof of the table (ARCHITECTURE §3.4). -/
theorem ofCode?_toCode (t : FrameType) : ofCode? (toCode t) = some t := by
  cases t <;> rfl

end FrameType

/-! ## The `GoAway` reason codes -/

/-- Why a peer ended the session. -/
inductive GoAwayCode where
  /-- An orderly end. -/
  | normal
  /-- The peer saw a protocol violation. -/
  | protocolError
  /-- The peer failed internally. -/
  | internalError
  deriving Repr, DecidableEq, BEq, Hashable

namespace GoAwayCode

/-- The wire code of a reason. -/
def toCode : GoAwayCode → Nat
  | .normal => 0
  | .protocolError => 1
  | .internalError => 2

/-- The reason a wire code names, if it names one. -/
def ofCode? : Nat → Option GoAwayCode
  | 0 => some .normal
  | 1 => some .protocolError
  | 2 => some .internalError
  | _ => none

/-- The table round trip for the reason codes. -/
theorem ofCode?_toCode (c : GoAwayCode) : ofCode? (toCode c) = some c := by
  cases c <;> rfl

end GoAwayCode

/-! ## Flags -/

/-- The four flag bits of a yamux frame. A frame carries any combination,
so the set is a product of four decisions and not an inductive. -/
structure Flags where
  /-- Stream open request. -/
  syn : Bool
  /-- Stream open acknowledgement. -/
  ack : Bool
  /-- The sender's write direction is finished. -/
  fin : Bool
  /-- Both directions abort. -/
  rst : Bool
  deriving Repr, DecidableEq, BEq, Hashable

namespace Flags

/-- No flag set. The name avoids `Option.none`: the four-bit word has
exactly one empty value, and a reader should not confuse it with an
absent one. -/
def empty : Flags := ⟨false, false, false, false⟩

/-- The 16-bit value of the flag word, as the specification lays it out:
`SYN` is bit 0, `ACK` bit 1, `FIN` bit 2, `RST` bit 3. -/
def toCode (f : Flags) : Nat :=
  (if f.syn then 1 else 0) + (if f.ack then 2 else 0) +
    (if f.fin then 4 else 0) + (if f.rst then 8 else 0)

/-- The flags a 16-bit value names, if it names any. A value with a bit
set above `RST` is not a flag word the specification defines, so the
decoder rejects it (ARCHITECTURE §4.8: a strict decode at the
boundary). -/
def ofCode? (n : Nat) : Option Flags :=
  if n < 16 then
    some
      { syn := n % 2 == 1
        ack := n / 2 % 2 == 1
        fin := n / 4 % 2 == 1
        rst := n / 8 % 2 == 1 }
  else
    none

/-- Every flag word fits in four bits, so it fits in the 16-bit field. -/
theorem toCode_lt_sixteen (f : Flags) : toCode f < 16 := by
  rcases f with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The four bits a code names reconstruct the code. The statement is
decided over `Fin 16`, so the kernel checks all sixteen values. -/
theorem toCode_ofBits (i : Fin 16) :
    toCode
        { syn := i.val % 2 == 1
          ack := i.val / 2 % 2 == 1
          fin := i.val / 4 % 2 == 1
          rst := i.val / 8 % 2 == 1 } = i.val := by
  revert i
  decide

/-- The table round trip for the flag word. -/
theorem ofCode?_toCode (f : Flags) : ofCode? (toCode f) = some f := by
  rcases f with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- A code that decodes names a value below the field width. -/
theorem lt_sixteen_of_ofCode?_eq_some {n : Nat} {f : Flags}
    (h : ofCode? n = some f) : n < 16 := by
  by_cases hn : n < 16
  · exact hn
  · simp [ofCode?, hn] at h

/-- A code that decodes is the code of the flags it names. -/
theorem toCode_eq_of_ofCode?_eq_some {n : Nat} {f : Flags}
    (h : ofCode? n = some f) : toCode f = n := by
  have hn : n < 16 := lt_sixteen_of_ofCode?_eq_some h
  have hf :
      f = { syn := n % 2 == 1
            ack := n / 2 % 2 == 1
            fin := n / 4 % 2 == 1
            rst := n / 8 % 2 == 1 } := by
    simp [ofCode?, hn] at h
    exact h.symm
  subst hf
  exact toCode_ofBits ⟨n, hn⟩

/-- The model encoding of a flag word: two bytes, high first. -/
def encode (f : Flags) : List Nat := [toCode f / 256 % 256, toCode f % 256]

/-- Every byte of an encoded flag word is below 256, so the header codec
needs no range check on the flag field. -/
theorem encode_lt (f : Flags) : ∀ b ∈ encode f, b < 256 := by
  intro b hb
  simp [encode] at hb
  rcases hb with rfl | rfl <;> exact Nat.mod_lt _ (by decide)


/-- The model decoding of a flag word. A short input is `truncated`; a
high byte that is not zero, or a low byte above the four defined bits,
is `malformed` (ARCHITECTURE §3.2, §5.2). -/
def decode? : List Nat → Except Bytes.DecodeError (Flags × List Nat)
  | hi :: lo :: rest =>
      if hi = 0 then
        match ofCode? lo with
        | some f => .ok (f, rest)
        | none => .error .malformed
      else
        .error .malformed
  | _ => .error .truncated

/-- Every flag word decodes from its own encoding. -/
theorem decode?_encode (f : Flags) : decode? (encode f) = .ok (f, []) := by
  have h16 : toCode f < 16 := toCode_lt_sixteen f
  have h256 : toCode f < 256 := by omega
  have hdiv : toCode f / 256 = 0 := Nat.div_eq_of_lt h256
  have hmod : toCode f % 256 = toCode f := Nat.mod_eq_of_lt h256
  simp [encode, decode?, hdiv, hmod, ofCode?_toCode]

/-- Every accepted input re-encodes to itself. -/
theorem encode_decode? : ∀ {bs : List Nat} {f : Flags} {rest : List Nat},
    decode? bs = .ok (f, rest) → encode f ++ rest = bs
  | [], _, _, h => by simp [decode?] at h
  | [_], _, _, h => by simp [decode?] at h
  | hi :: lo :: rs, f, rest, h => by
      simp only [decode?] at h
      split at h
      · rename_i hhi
        split at h
        · rename_i g hg
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hgf, hgr⟩ := h
          have hlo : lo < 16 := lt_sixteen_of_ofCode?_eq_some hg
          have hcode : toCode g = lo := toCode_eq_of_ofCode?_eq_some hg
          have h256 : lo < 256 := by omega
          have hgoal : encode g ++ rs = hi :: lo :: rs := by
            simp [encode, hhi, hcode, Nat.div_eq_of_lt h256, Nat.mod_eq_of_lt h256]
          rw [← hgf, ← hgr]
          exact hgoal
        · simp at h
      · simp at h

/-- The `Bytes.Codec` instance for the flag word (ARCHITECTURE §3.2). -/
instance : Bytes.Codec Flags where
  encode := encode
  decode? := decode?

/-- The flag codec is lawful: decode after encode returns the value and
consumes exactly its bytes (ARCHITECTURE §6, layer 1). -/
instance : Bytes.LawfulCodec Flags where
  decodeEncode := decode?_encode
  encodeDecode := fun _ _ _ h => encode_decode? h

end Flags

end Yamux
