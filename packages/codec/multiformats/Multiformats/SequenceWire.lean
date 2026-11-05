import Multiformats.ComponentWire

/-!
# Validated sequences of wire components

The framing proofs are independent of address semantics. A caller
supplies a Boolean check for the complete sequence, including its total
budget and any ordering rules. Only sequences that pass it are values
of the codec. Text presentation is outside this wire model.
-/

set_option autoImplicit false

namespace Multiformats.SequenceWire

open ComponentWire (Frame)

/-- The whole-sequence check is carried as a fact in the value's type. -/
structure Value (accept : List Frame → Bool) where
  frames : List Frame
  valid : accept frames = true
  deriving DecidableEq, Repr

/-- Each component emits its tag next to its value. -/
def encodeFrames : List Frame → List Nat
  | [] => []
  | frame :: rest => ComponentWire.encode frame ++ encodeFrames rest

/-- The production sequence encoder reuses one byte builder for every component. -/
def encodeFramesB (frames : List Frame) : ByteArray :=
  frames.foldl (fun output frame => ComponentWire.appendB frame output) ByteArray.empty

/-- Counting framed component sizes gives the exact address length without allocation. -/
theorem encodeFramesLength (frames : List Frame) :
    (frames.map ComponentWire.encodedLength).sum = (encodeFrames frames).length := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp only [List.map_cons, List.sum_cons, ComponentWire.encodedLengthEq,
        encodeFrames, List.length_append, ih]

/-- A complete sequence cannot emit a model entry outside the byte range. -/
theorem encodeFramesBytes (frames : List Frame) : ∀ b ∈ encodeFrames frames, b < 256 := by
  induction frames with
  | nil => simp [encodeFrames]
  | cons frame frames ih =>
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ComponentWire.encodeBytes frame b hb
      · exact ih b hb

/-- The decoder has fuel for at most one step per input byte. -/
def decodeFrames : Nat → List Nat → Except Error (List Frame)
  | fuel, input =>
      if input = [] then .ok []
      else match fuel with
      | 0 => .error (.framing .malformed)
      | fuel + 1 => do
          let (frame, rest) ← ComponentWire.decodeAt? input
          let frames ← decodeFrames fuel rest
          .ok (frame :: frames)

/-- A tail-recursive reader keeps stack use bounded for long component sequences. -/
private def decodeFramesLoop : Nat → List Nat → List Frame → Except Error (List Frame)
  | fuel, input, reversed =>
      if input = [] then .ok reversed.reverse
      else match fuel with
      | 0 => .error (.framing .malformed)
      | fuel + 1 => do
          let (frame, rest) ← ComponentWire.decodeAt? input
          decodeFramesLoop fuel rest (frame :: reversed)

/-- The accumulator reader has exactly the model's values and errors. -/
private theorem decodeFramesLoopEq (fuel : Nat) (input : List Nat) (reversed : List Frame) :
    decodeFramesLoop fuel input reversed =
      (decodeFrames fuel input).map (fun frames => reversed.reverse ++ frames) := by
  induction fuel generalizing input reversed with
  | zero =>
      by_cases empty : input = [] <;> simp [decodeFramesLoop, decodeFrames, empty, Except.map]
  | succ fuel ih =>
      by_cases empty : input = []
      · simp [decodeFramesLoop, decodeFrames, empty, Except.map]
      · simp only [decodeFramesLoop, decodeFrames, ite_eq_right empty]
        cases hc : ComponentWire.decodeAt? input with
        | error error => simp [Bind.bind, Except.bind, Except.map]
        | ok pair =>
            obtain ⟨frame, rest⟩ := pair
            simp only [Bind.bind, Except.bind]
            rw [ih]
            cases ht : decodeFrames fuel rest <;>
              simp [Except.map, List.reverse_cons, List.append_assoc]

/-- The empty accumulator starts the checked tail-recursive reader. -/
private def decodeFramesTail (fuel : Nat) (input : List Nat) : Except Error (List Frame) :=
  decodeFramesLoop fuel input []

/-- Compilation uses the proved accumulator reader without changing the model's definition. -/
@[csimp] theorem decodeFramesEqLoop : decodeFrames = decodeFramesTail := by
  funext fuel input
  symm
  cases hd : decodeFrames fuel input <;>
    simpa [decodeFramesTail, hd, Except.map] using decodeFramesLoopEq fuel input []

/-- FlatMap uses the standard library's tail-recursive implementation. -/
private def encodeFramesTail (frames : List Frame) : List Nat :=
  frames.flatMap ComponentWire.encode

/-- The standard flatMap compiler path avoids a stack frame per encoded component. -/
@[csimp] theorem encodeFramesEqFlatMap :
    encodeFrames = encodeFramesTail := by
  funext frames
  unfold encodeFramesTail
  induction frames with
  | nil => rfl
  | cons frame frames ih => simp only [encodeFrames, List.flatMap_cons, ih]

/-- A checked sequence reuses the unambiguous component encoding. -/
def encode {accept : List Frame → Bool} (value : Value accept) : List Nat :=
  encodeFrames value.frames

/-- Framing completes before the caller's whole-sequence check is evaluated. -/
def decode? (accept : List Frame → Bool) (input : List Nat) :
    Except Error (Value accept × List Nat) := do
  let frames ← decodeFrames input.length input
  if h : accept frames = true then .ok (⟨frames, h⟩, []) else .error .badAddress

/-- Every nonempty list has a nonempty encoded first component. -/
theorem encodeFramesNonempty (frame : Frame) (frames : List Frame) :
    encodeFrames (frame :: frames) ≠ [] := by
  intro h
  have first := ComponentWire.encodeNonempty frame
  have lengths := congrArg List.length h
  have positive := List.length_pos_iff.mpr first
  simp only [encodeFrames, List.length_append, List.length_nil] at lengths
  omega

/-- The input length supplies enough fuel for every valid component list. -/
theorem decodeFramesEncode (frames : List Frame) (fuel : Nat)
    (enough : (encodeFrames frames).length ≤ fuel) :
    decodeFrames fuel (encodeFrames frames) = .ok frames := by
  induction frames generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons frame frames ih =>
      have nonempty := encodeFramesNonempty frame frames
      have positive := List.length_pos_iff.mpr (ComponentWire.encodeNonempty frame)
      simp only [encodeFrames, List.length_append] at enough
      cases fuel with
      | zero => omega
      | succ fuel =>
          have tail : (encodeFrames frames).length ≤ fuel := by omega
          rw [encodeFrames, decodeFrames]
          simp only [show ComponentWire.encode frame ++ encodeFrames frames ≠ [] from nonempty,
            ite_false, ComponentWire.decodeEncodeSuffix, Bind.bind, Except.bind,
            ih fuel tail]

/-- Distinct ordered component sequences have distinct wire encodings. -/
theorem encodeFramesInjective (left right : List Frame)
    (same : encodeFrames left = encodeFrames right) : left = right := by
  have decoded := decodeFramesEncode left (encodeFrames left).length (Nat.le_refl _)
  rw [same, decodeFramesEncode right _ (Nat.le_refl _)] at decoded
  exact (Except.ok.inj decoded).symm

/-- Any accepted sequence retains its complete representation after decoding. -/
theorem decodeEncode (accept : List Frame → Bool) (value : Value accept) :
    decode? accept (encode value) = .ok (value, []) := by
  have h := decodeFramesEncode value.frames (encode value).length (Nat.le_refl _)
  simp only [encode] at h
  simp only [decode?, encode, h, Bind.bind, Except.bind, dite_eq_left value.valid]

/-- Every successful raw parse reconstructs all input bytes. -/
theorem decodeFramesOk (fuel : Nat) (input : List Nat) (frames : List Frame)
    (h : decodeFrames fuel input = .ok frames) : input = encodeFrames frames := by
  induction fuel generalizing input frames with
  | zero =>
      simp only [decodeFrames] at h
      split at h
      · rename_i empty
        subst input
        cases h
        rfl
      · cases h
  | succ fuel ih =>
      rw [decodeFrames] at h
      split at h
      · rename_i empty
        subst input
        cases h
        rfl
      · cases hc : ComponentWire.decodeAt? input with
        | error error => simp [hc, Bind.bind, Except.bind] at h
        | ok pair =>
            obtain ⟨frame, rest⟩ := pair
            simp only [hc, Bind.bind, Except.bind] at h
            cases ht : decodeFrames fuel rest with
            | error error => simp [ht] at h
            | ok tail =>
                simp only [ht] at h
                cases h
                have split := ComponentWire.encodeDecode input frame rest hc
                have suffix := ih rest tail ht
                simpa only [encodeFrames] using
                  split.trans (congrArg (ComponentWire.encode frame ++ ·) suffix)

/-- The whole-sequence check can reject values but cannot change their bytes. -/
theorem encodeDecode (accept : List Frame → Bool) (input : List Nat)
    (value : Value accept) (rest : List Nat)
    (h : decode? accept input = .ok (value, rest)) : input = encode value ++ rest := by
  cases hd : decodeFrames input.length input with
  | error error => simp [decode?, hd, Bind.bind, Except.bind] at h
  | ok frames =>
      simp only [decode?, hd, Bind.bind, Except.bind] at h
      split at h
      · have he := Prod.mk.inj (Except.ok.inj h)
        rcases he with ⟨rfl, rfl⟩
        simpa only [encode, List.append_nil] using decodeFramesOk input.length input frames hd
      · cases h

/-- The cursor advances for every component, including valueless ones. -/
private def decodeLoopB (input : ByteArray) : Nat → Nat → List Frame → Except Error (List Frame)
  | fuel, position, reversed =>
      if position = input.size then .ok reversed.reverse
      else match fuel with
      | 0 => .error (.framing .malformed)
      | fuel + 1 => do
          let (frame, next) ← ComponentWire.decodeAtB? input position
          if next ≤ position then .error (.framing .malformed)
          else decodeLoopB input fuel next (frame :: reversed)

/-- The production path validates the same sequence after independent cursor parsing. -/
def decodeB? (accept : List Frame → Bool) (input : ByteArray) : Except Error (Value accept × Nat) := do
  let frames ← decodeLoopB input input.size 0 []
  if h : accept frames = true then .ok (⟨frames, h⟩, input.size) else .error .badAddress

/-- The generic codec classes belong to the wrapped, validated sequence. -/
instance (accept : List Frame → Bool) : Bytes.Codec (Value accept) where
  encode := encode
  decode? input := (decode? accept input).mapError Error.toDecodeError

/-- A caller adds no axiom by supplying a computable validation rule. -/
instance (accept : List Frame → Bool) : Bytes.LawfulCodec (Value accept) where
  decodeEncode value := by
    change (decode? accept (encode value)).mapError Error.toDecodeError = _
    rw [decodeEncode]
    rfl
  encodeDecode input value rest h := by
    change (decode? accept input).mapError Error.toDecodeError = .ok (value, rest) at h
    cases hd : decode? accept input with
    | error error => simp [hd, Except.mapError] at h
    | ok pair =>
        simp only [hd, Except.mapError, Except.ok.injEq] at h
        cases h
        exact (encodeDecode accept input value rest hd).symm

end Multiformats.SequenceWire
