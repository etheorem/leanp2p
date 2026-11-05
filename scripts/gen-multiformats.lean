import Std

/-!
# Generate the committed multiformats tables

Run `lake env lean --run scripts/gen-multiformats.lean` to regenerate
the tables. `--check` compares the generated source with the committed
file. Only the pinned vendor copies are read; generation needs no network.
-/

set_option autoImplicit false

namespace GenerateMultiformats

/-- Only registry names become identifiers. Numeric codes remain unchanged. -/
private def ident (s : String) : String :=
  "«" ++ s.replace "libp2p" "p2p" ++ "»"

/-- CSV descriptions may contain commas; the consumed leading columns do not. -/
private def readRows (path : System.FilePath) : IO (List (List String)) := do
  let text ← IO.FS.readFile path
  pure ((text.splitOn "\n").drop 1 |>.filterMap fun line =>
    if line.trimAscii.toString.isEmpty then none
    else some ((line.splitOn ",").map (·.trimAscii.toString)))

/-- A malformed source row stops generation instead of silently dropping data. -/
private def cell (row : List String) (n : Nat) : IO String :=
  match row[n]? with
  | some s => pure s
  | none => throw <| IO.userError "registry row has too few columns"

/-- Registries use decimal numbers and hexadecimal codes with a 0x prefix. -/
private def number (s : String) : IO Nat := do
  let normalized := s.toLower
  let (base, chars) := if normalized.startsWith "0x" then (16, normalized.toList.drop 2)
    else (10, normalized.toList)
  if chars.isEmpty then throw <| IO.userError "empty registry number"
  chars.foldlM (fun value c => do
    let digit := if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else base
    if digit ≥ base then throw <| IO.userError s!"invalid registry number: {s}"
    pure (value * base + digit)) 0

/-- Every code has one canonical constructor. Aliases remain in the metadata. -/
private def uniqueCodes (rows : List (String × Nat)) : List (String × Nat) :=
  rows.foldl (fun acc row => if acc.any (·.2 == row.2) then acc else acc ++ [row]) []

/-- Balanced comparisons keep kernel reduction short even for the full registry. -/
private def lookupTree : Nat → List (String × Nat) → String → String
  | 0, _, _ => "none"
  | _ + 1, [], _ => "none"
  | _ + 1, [(name, code)], _ =>
      s!"if code = {code} then some .{ident name} else none"
  | fuel + 1, rows, indent =>
      let sorted := rows.mergeSort (fun a b => a.2 ≤ b.2)
      let middle := sorted.length / 2
      let pivot := (sorted[middle]?.getD ("", 0)).2
      s!"if code < {pivot} then\n{indent}  "
        ++ lookupTree fuel (sorted.take middle) (indent ++ "  ")
        ++ s!"\n{indent}else\n{indent}  "
        ++ lookupTree fuel (sorted.drop middle) (indent ++ "  ")

/-- Emit a closed set and the inverse law used by every consumer. -/
private def enumSource (name : String) (rows : List (String × Nat))
    (withNames : Bool) : String := Id.run do
  let mut out := s!"/-- Canonical members of the pinned {name} registry. -/\ninductive {name} where\n"
  for (label, _) in rows do out := out ++ s!"  | {ident label}\n"
  out := out ++ "  deriving DecidableEq, Repr, Hashable\n\n"
  out := out ++ s!"/-- The numeric code is registry data. -/\ndef {name}.toCode : {name} → Nat\n"
  for (label, code) in rows do out := out ++ s!"  | .{ident label} => {code}\n"
  out := out ++ s!"\n/-- Unknown codes have no constructor. -/\ndef {name}.ofCode? (code : Nat) : Option {name} :=\n  "
  out := out ++ lookupTree rows.length rows "  " ++ "\n\n"
  out := out ++ s!"set_option maxRecDepth 4096 in\n/-- Every constructor is recovered from its wire code. -/\n@[simp] theorem {name}.ofCodeToCode (value : {name}) :\n    ofCode? value.toCode = some value := by\n  cases value <;> rfl\n\n"
  out := out ++ "/-- Equal codes identify the same canonical registry member. -/\ntheorem "
    ++ name ++ ".toCodeInjective {a b : " ++ name
    ++ s!"} (h : a.toCode = b.toCode) : a = b := by\n  have hi := congrArg {name}.ofCode? h\n  simpa only [{name}.ofCodeToCode, Option.some.injEq] using hi\n\n"
  out := out ++ s!"set_option maxRecDepth 4096 in\n/-- Every registry code fits the shared nine-byte varint budget. -/\ntheorem {name}.codeLt (value : {name}) : value.toCode < 2 ^ 63 := by\n  cases value <;> decide\n\n"
  out := out ++ s!"set_option maxRecDepth 4096 in\n/-- The complete canonical set, in source order. -/\ndef {name}.all : List {name} :=\n  ["
  out := out ++ String.intercalate ", " (rows.map fun (label, _) => "." ++ ident label)
  out := out ++ "]\n\n"
  if withNames then
    out := out ++ s!"/-- The canonical spelling from the registry. -/\ndef {name}.name : {name} → String\n"
    for (label, _) in rows do out := out ++ s!"  | .{ident label} => {reprStr label}\n"
    out := out ++ "\n"
  return out

/-- The complete output is deterministic in the pinned inputs. -/
private def generate : IO String := do
  let codecRows ← readRows "vendor/multicodec/table.csv"
  let mut codecs : List (String × Nat) := []
  let mut hashes : List (String × Nat) := []
  for row in codecRows do
    let name ← cell row 0
    let tag ← cell row 1
    let code ← number (← cell row 2)
    codecs := codecs ++ [(name, code)]
    if tag == "multihash" || tag == "hash" then hashes := hashes ++ [(name, code)]
  if (uniqueCodes codecs).length != codecs.length then
    throw <| IO.userError "multicodec contains duplicate numeric codes"

  let protocolRows ← readRows "vendor/multiaddr/protocols.csv"
  let mut protocols : List (String × Nat) := []
  let mut protocolMeta : List (String × Nat × Option Nat) := []
  for row in protocolRows do
    let code ← number (← cell row 0)
    let size ← cell row 1
    let name ← cell row 2
    let bits ← if size == "V" then pure none else some <$> number size
    protocols := protocols ++ [(name, code)]
    protocolMeta := protocolMeta ++ [(name, code, bits)]
  protocols := uniqueCodes protocols

  let baseRows ← readRows "vendor/multibase/multibase.csv"
  let mut bases : List (String × Nat) := []
  let mut baseMeta : List (Nat × String × String) := []
  for row in baseRows do
    let unicode ← cell row 0
    let code ← number ("0x" ++ String.ofList (unicode.toList.drop 2))
    let name ← cell row 2
    let status ← cell row 4
    baseMeta := baseMeta ++ [(code, name, status)]
    if name != "none" && status != "reserved" then bases := bases ++ [(name, code)]

  let emojiText ← IO.FS.readFile "vendor/multibase/rfcs/Base256Emoji.md"
  let mut emojiCodes : List Nat := []
  for line in emojiText.splitOn "\n" do
    let columns := (line.splitOn "|").map (·.trimAscii.toString)
    if (columns[2]?.getD "").startsWith "U+" then
      let index ← number (← cell columns 3)
      if index != emojiCodes.length then
        throw <| IO.userError "emoji registry indices are not contiguous"
      let code ← number ("0x" ++ String.ofList ((← cell columns 2).toList.drop 2))
      emojiCodes := emojiCodes ++ [code]
  if emojiCodes.length != 256 then throw <| IO.userError "emoji registry must contain 256 rows"

  let codecPin := (← IO.FS.readFile "vendor/multicodec/.pin").trimAscii.toString
  let protocolPin := (← IO.FS.readFile "vendor/multiaddr/.pin").trimAscii.toString
  let basePin := (← IO.FS.readFile "vendor/multibase/.pin").trimAscii.toString
  let mut out := "import Std\n\n/-!\n# Generated registry tables\n\nGenerated by scripts/gen-multiformats.lean. Edit the pinned sources\nand regenerate instead of changing this file by hand.\n\n"
  out := out ++ s!"Multicodec: {codecPin}\nMultiaddr: {protocolPin}\nMultibase: {basePin}\n"
  out := out ++ "-/\n\nset_option autoImplicit false\n\nnamespace Multiformats\n\n"
  out := out ++ enumSource "HashCode" hashes true
  out := out ++ enumSource "ContentCodec" codecs false
  out := out ++ enumSource "Protocol" protocols true
  out := out ++ "/-- Text aliases retain their source row while resolving to a canonical member. -/\ndef Protocol.ofName? : String → Option Protocol\n"
  for (name, code, _) in protocolMeta do
    let canonical := (protocols.find? (·.2 == code)).getD (name, code)
    out := out ++ s!"  | {reprStr name} => some .{ident canonical.1}\n"
  out := out ++ "  | _ => none\n\n"
  out := out ++ "/-- The size column as published, before documented wire corrections. -/\ndef Protocol.declaredBits? : Protocol → Option Nat\n"
  for (name, _) in protocols do
    let bits := ((protocolMeta.find? (·.1 == name)).getD (name, 0, none)).2.2
    out := out ++ s!"  | .{ident name} => " ++ (match bits with | none => "none" | some n => s!"some {n}") ++ "\n"
  out := out ++ "\n/-- Memory uses the fixed eight-byte form documented by the package. -/\ndef Protocol.fixedBytes? (protocol : Protocol) : Option Nat :=\n  if protocol = .«memory» then some 8 else protocol.declaredBits?.map (· / 8)\n\n"
  out := out ++ "/-- All published protocol rows, including aliases. -/\ndef Protocol.registryRows : List (Nat × Option Nat × String) :=\n  ["
  out := out ++ String.intercalate ", " (protocolMeta.map fun (name, code, bits) =>
    s!"({code}, " ++ (match bits with | none => "none" | some n => s!"some {n}") ++ s!", {reprStr name})")
  out := out ++ "]\n\nnamespace Multibase\n\n"
  out := out ++ enumSource "Base" bases true
  out := out ++ "/-- Multibase prefixes are Unicode code points. -/\ndef Base.prefixChar (base : Base) : Char := Char.ofNat base.toCode\n\n"
  out := out ++ "/-- Reserved rows stay visible without becoming supported encodings. -/\ndef Base.registryRows : List (Nat × String × String) :=\n  ["
  out := out ++ String.intercalate ", " (baseMeta.map fun (code, name, status) => s!"({code}, {reprStr name}, {reprStr status})")
  out := out ++ "]\n\n/-- The pinned RFC maps each byte to one Unicode scalar value. -/\ndef emojiAlphabet : List Char :=\n  ["
  out := out ++ String.intercalate ", " (emojiCodes.map fun code => s!"Char.ofNat {code}")
  out := out ++ "]\n\nend Multibase\n\nend Multiformats\n"
  pure out

end GenerateMultiformats

/-- Regenerate the file, or check it without changing the working tree. -/
def main (args : List String) : IO UInt32 := do
  let output ← GenerateMultiformats.generate
  let path : System.FilePath := "packages/codec/multiformats/Multiformats/Tables.lean"
  if args == ["--check"] then
    if (← IO.FS.readFile path) == output then
      IO.println "multiformats tables match the pinned registries"
      pure 0
    else
      IO.eprintln "multiformats tables are stale; rerun scripts/gen-multiformats.lean"
      pure 1
  else if args.isEmpty then
    IO.FS.writeFile path output
    IO.println s!"wrote {path}"
    pure 0
  else
    IO.eprintln "usage: lake env lean --run scripts/gen-multiformats.lean [--check]"
    pure 1
