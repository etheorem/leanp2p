import Multiformats.Error

/-!
# Strict IP text conversions

Decimal parsing checks ASCII digits explicitly. IPv4 rejects leading
zeros. IPv6 uses the first longest zero run, and prints mapped IPv4
addresses in the dotted form required by the package contract.
-/

set_option autoImplicit false

namespace Multiformats.Multiaddr

/-- Parsing stops at the exclusive bound before building a large integer. -/
def decimal? (text : String) (bound : Nat) : Except Error Nat := do
  if text.isEmpty then .error .badValue
  else
    text.toList.foldlM (fun value c =>
      if '0' ≤ c ∧ c ≤ '9' then
        let next := value * 10 + c.toNat - '0'.toNat
        if next < bound then .ok next else .error .badValue
      else .error .badValue) 0

/-- A leading zero would make the address ambiguous to other parsers. -/
private def octet? (text : String) : Except Error Nat := do
  let n ← decimal? text 256
  if text.length = 1 || text.toList.head? != some '0' then .ok n else .error .badValue

/-- The four octets are already the four bytes of the wire value. -/
def parseIp4? (text : String) : Except Error (List Nat) := do
  match text.splitOn "." with
  | [a, b, c, d] => .ok [← octet? a, ← octet? b, ← octet? c, ← octet? d]
  | _ => .error .badValue

/-- A text formatter refuses an invalid wire shape. -/
def ip4String? (bytes : List Nat) : Except Error String :=
  match bytes with
  | [a, b, c, d] =>
      if bytes.all (· < 256) then .ok s!"{a}.{b}.{c}.{d}" else .error .badValue
  | _ => .error .badValue

/-- A checked IPv4 value always has a printable text form. -/
theorem ip4StringValid (bytes : List Nat) (length : bytes.length = 4)
    (bounded : ∀ b ∈ bytes, b < 256) : ∃ text, ip4String? bytes = .ok text := by
  have allBytes : bytes.all (· < 256) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using bounded
  match bytes with
  | [a, b, c, d] =>
      refine ⟨s!"{a}.{b}.{c}.{d}", ?_⟩
      simp only [ip4String?, allBytes, ite_true]
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => simp at length

/-- Hex groups allow at most four ASCII digits. -/
private def group? (text : String) : Except Error Nat := do
  if text.isEmpty || text.length > 4 then .error .badValue
  else
    text.toList.foldlM (fun value c =>
      let digit := if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
        else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 97 + 10)
        else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 65 + 10) else none
      match digit with
      | some d => .ok (value * 16 + d)
      | none => .error .badValue) 0

/-- An empty half is permitted only around the one compressed zero run. -/
private def groups? (text : String) : Except Error (List Nat) :=
  if text.isEmpty then .ok [] else (text.splitOn ":").mapM group?

/-- Hexadecimal output has no leading zeros. -/
private def hexGroup (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Dotted tails become two sixteen-bit groups before compression is expanded. -/
private def expandDotted? (text : String) : Except Error String := do
  if !text.contains '.' then .ok text
  else
    let parts := text.splitOn ":"
    let tail ← match parts.getLast? with
      | none => .error .badValue
      | some tail => .ok tail
    match (← parseIp4? tail) with
    | [a, b, c, d] =>
        .ok (String.intercalate ":" parts.dropLast ++ ":" ++
          hexGroup (a * 256 + b) ++ ":" ++ hexGroup (c * 256 + d))
    | _ => .error .badValue

/-- Eight expanded groups produce exactly sixteen big-endian bytes. -/
def parseIp6? (input : String) : Except Error (List Nat) := do
  let text ← expandDotted? input
  let groups ← if text.contains "::" then
      match text.splitOn "::" with
      | [left, right] => do
          let l ← groups? left
          let r ← groups? right
          let fill := 8 - l.length - r.length
          if fill = 0 then .error .badValue else .ok (l ++ List.replicate fill 0 ++ r)
      | _ => .error .badValue
    else do
      let groups ← (text.splitOn ":").mapM group?
      if groups.length = 8 then .ok groups else .error .badValue
  .ok (groups.flatMap fun n => [n / 256, n % 256])

/-- Adjacent bytes form one sixteen-bit group. -/
private def pairGroups : List Nat → List Nat
  | a :: b :: rest => (a * 256 + b) :: pairGroups rest
  | _ => []

/-- RFC 5952 compression uses the leftmost run when two runs have equal length. -/
def ip6String? (bytes : List Nat) : Except Error String := do
  if bytes.length != 16 || !bytes.all (· < 256) then .error .badValue
  else
    let groups := pairGroups bytes
    if (groups.take 5).all (· == 0) && groups[5]?.getD 0 == 65535 then
      let a := groups[6]?.getD 0
      let b := groups[7]?.getD 0
      .ok s!"::ffff:{a / 256}.{a % 256}.{b / 256}.{b % 256}"
    else
      let best := (List.range 8).foldl (fun best start =>
        let count := ((groups.drop start).takeWhile (· == 0)).length
        match best with
        | none => if count ≥ 2 then some (start, count) else none
        | some (_, length) => if count > length then some (start, count) else best) none
      match best with
      | none => .ok (String.intercalate ":" (groups.map hexGroup))
      | some (start, count) =>
          .ok (String.intercalate ":" ((groups.take start).map hexGroup) ++ "::" ++
            String.intercalate ":" ((groups.drop (start + count)).map hexGroup))

/-- The byte invariant makes every IPv6 formatting branch successful. -/
theorem ip6StringValid (bytes : List Nat) (length : bytes.length = 16)
    (bounded : ∀ b ∈ bytes, b < 256) : ∃ text, ip6String? bytes = .ok text := by
  have allBytes : bytes.all (· < 256) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using bounded
  unfold ip6String?
  split
  · rename_i rejected
    simp [length, allBytes] at rejected
  · dsimp only
    split
    · exact ⟨_, rfl⟩
    · split <;> exact ⟨_, rfl⟩

end Multiformats.Multiaddr
