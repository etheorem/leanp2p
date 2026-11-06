import Bytes.Error

/-!
# Taking a payload

A length-prefixed payload on the wire is "a length, then that many
bytes". Every codec above reads the bytes the same way, so the step has
one home here: `take?` splits the model input at a length and reports
the two failures a reader must tell apart (ARCHITECTURE §3.2, §5.2).
The length cap belongs to the caller, which checks it before the take.
`sliceAt?` is the same step on `ByteArray`, for the decoders that walk
the wire bytes by offset.
-/

set_option autoImplicit false

namespace Bytes

/-- The first `k` bytes of the input, and the rest. A non-byte among the
bytes present is `malformed`: no suffix can repair it. Fewer than `k`
bytes is `truncated`: more input may complete the payload. -/
def take? (k : Nat) (l : List Nat) : Except DecodeError (List Nat × List Nat) :=
  if ¬∀ x ∈ l.take k, x < 256 then .error .malformed
  else if l.length < k then .error .truncated
  else .ok (l.take k, l.drop k)

/-- Bytes in front of any rest take back out whole. -/
theorem take?Append {b : List Nat} (rest : List Nat) (h : ∀ x ∈ b, x < 256) :
    take? b.length (b ++ rest) = .ok (b, rest) := by
  have htake : (b ++ rest).take b.length = b := by simp
  unfold take?
  rw [htake]
  split
  · next hn => exact absurd h hn
  · split
    · next hl => simp at hl; omega
    · simp

/-- A successful take split the input at `k`, and the taken part holds
bytes. -/
theorem ofTake? {k : Nat} {l b rest : List Nat} (h : take? k l = .ok (b, rest)) :
    b ++ rest = l ∧ b.length = k ∧ ∀ x ∈ b, x < 256 := by
  unfold take? at h
  split at h
  · cases h
  · next hbytes =>
    split at h
    · cases h
    · next hlen =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨List.take_append_drop k l, ?_, by simpa using hbytes⟩
      simp only [List.length_take]
      omega

/-- A take from an input shorter than `k` that holds bytes is
`truncated`: more input can complete the payload. -/
theorem take?Short {k : Nat} {l : List Nat} (hb : ∀ x ∈ l, x < 256) (hl : l.length < k) :
    take? k l = .error .truncated := by
  have hall : ∀ x ∈ l.take k, x < 256 := fun x hx => hb x (List.mem_of_mem_take hx)
  unfold take?
  rw [ite_eq_right (fun hn => hn hall), ite_eq_left hl]

/-- The `k` bytes at offset `pos` of `b`, and the offset after them:
`take?` on `ByteArray`, for a decoder that walks its input by offset.
`truncated` when the input ends first. A `ByteArray` holds bytes only,
so the `malformed` answer of `take?` cannot occur. The call copies the
`k` bytes and nothing else. -/
def sliceAt? (b : ByteArray) (pos k : Nat) : Except DecodeError (ByteArray × Nat) :=
  if pos + k ≤ b.size then .ok (b.extract pos (pos + k), pos + k) else .error .truncated

example : take? 2 [1, 2, 3] = .ok ([1, 2], [3]) := rfl
example : take? 4 [1, 2, 3] = .error .truncated := rfl
example : take? 2 [1, 300, 3] = .error .malformed := rfl

end Bytes
