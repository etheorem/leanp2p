/-!
# Muxer frame codec (pure, verified)

Framing: `[sid : u32le][len : u32le][payload]`. Modeled over the `List Nat`
byte model; the IO layer converts at the edge. A length-prefixed payload
also serves as EOF (empty payload = half-close) in the sim muxer.
-/

namespace LeanP2P.Framing

structure Frame where
  sid : Nat
  payload : List Nat
deriving Repr, BEq

def u32le (n : Nat) : List Nat :=
  [n % 256, n / 256 % 256, n / 65536 % 256, n / 16777216 % 256]

def fromU32le : List Nat → Nat
  | [a, b, c, d] => a + 256 * b + 65536 * c + 16777216 * d
  | _ => 0

theorem fromU32le_u32le (n : Nat) (h : n < 4294967296) : fromU32le (u32le n) = n := by
  simp only [u32le, fromU32le]
  omega

theorem u32le_len (n : Nat) : (u32le n).length = 4 := by
  simp [u32le]

def encode (f : Frame) : List Nat :=
  u32le f.sid ++ u32le f.payload.length ++ f.payload

def decode? : List Nat → Option (Frame × List Nat)
  | bs =>
    if 8 ≤ bs.length then
      if fromU32le ((bs.drop 4).take 4) ≤ (bs.drop 8).length then
        some ({ sid := fromU32le (bs.take 4),
                payload := (bs.drop 8).take (fromU32le ((bs.drop 4).take 4)) },
              (bs.drop 8).drop (fromU32le ((bs.drop 4).take 4)))
      else none
    else none

private theorem take4_of_len4 {l : List Nat} (h : l.length = 4) (t : List Nat) :
    (l ++ t).take 4 = l := by
  rw [← h, List.take_left]

private theorem drop4_of_len4 {l : List Nat} (h : l.length = 4) (t : List Nat) :
    (l ++ t).drop 4 = t := by
  rw [← h, List.drop_left]

theorem decode_eq (bs : List Nat) (h8 : 8 ≤ bs.length)
    (hlen : fromU32le ((bs.drop 4).take 4) ≤ (bs.drop 8).length) :
    decode? bs =
      some ({ sid := fromU32le (bs.take 4),
              payload := (bs.drop 8).take (fromU32le ((bs.drop 4).take 4)) },
            (bs.drop 8).drop (fromU32le ((bs.drop 4).take 4))) := by
  unfold decode?
  simp only [decode?]
  split
  · rfl
  · omega

/-- Decoding a serialized frame recovers it and consumes the whole buffer. -/
theorem decode_encode (f : Frame) (h1 : f.sid < 4294967296) (h2 : f.payload.length < 4294967296) :
    decode? (encode f) = some (f, []) := by
  have e : encode f = u32le f.sid ++ (u32le f.payload.length ++ f.payload) := rfl
  have h8 : 8 ≤ (u32le f.sid ++ (u32le f.payload.length ++ f.payload)).length := by
    simp only [List.length_append, u32le_len]
    omega
  have hsid : (u32le f.sid ++ (u32le f.payload.length ++ f.payload)).take 4 = u32le f.sid :=
    take4_of_len4 (u32le_len _) _
  have hlen : ((u32le f.sid ++ (u32le f.payload.length ++ f.payload)).drop 4).take 4
      = u32le f.payload.length := by
    rw [drop4_of_len4 (u32le_len _) _, take4_of_len4 (u32le_len _) _]
  have hrest : (u32le f.sid ++ (u32le f.payload.length ++ f.payload)).drop 8 = f.payload := by
    rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop,
      drop4_of_len4 (u32le_len _) _, drop4_of_len4 (u32le_len _) _]
  have hle : fromU32le (((u32le f.sid ++ (u32le f.payload.length ++ f.payload)).drop 4).take 4)
      ≤ ((u32le f.sid ++ (u32le f.payload.length ++ f.payload)).drop 8).length := by
    rw [hlen, fromU32le_u32le f.payload.length h2, hrest]; exact Nat.le_refl _
  rw [e, decode_eq _ h8 hle, hsid, hlen, hrest, fromU32le_u32le f.sid h1,
    fromU32le_u32le f.payload.length h2]
  simp

end LeanP2P.Framing
