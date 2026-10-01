import Tests.Support

/-!
# Multibase suite

Mirrors: multiformats/multibase tests/*.csv, pinned in VECTORS.lock and
extracted by scripts/extract-vectors.py.

- basic / leading_zero / two_leading_zeros: `encode` must produce the CSV
  value byte-exactly (the value includes the multibase prefix) and `decode?`
  must invert it.
- case_insensitivity: the CSV values are NON-canonical (mixed case), so only
  the decode direction is checked - mixed-case digits must decode to the
  same bytes for base16 / base32 / base32hex / base36 (and their pad and
  upper variants).
-/

open LeanP2P Tests

namespace Tests

def mbKind? : String → Option Multibase.Base
  | "base2" => some .base2 | "base8" => some .base8 | "base10" => some .base10
  | "base16" => some .base16 | "base16upper" => some .base16upper
  | "base32" => some .base32 | "base32upper" => some .base32upper
  | "base32hex" => some .base32hex | "base32hexupper" => some .base32hexupper
  | "base32pad" => some .base32pad
  | "base32padupper" | "base32pad-upper" => some .base32padupper
  | "base32hexpad" => some .base32hexpad
  | "base32hexpadupper" => some .base32hexpadupper
  | "base32z" => some .base32z | "base36" => some .base36
  | "base36upper" => some .base36upper | "base58btc" => some .base58btc
  | "base58flickr" => some .base58flickr | "base64" => some .base64
  | "base64pad" => some .base64pad | "base64url" => some .base64url
  | "base64urlpad" => some .base64urlpad
  | "base256emoji" => some .base256emoji
  | _ => none

def Multibase.run (r : Runner) : IO Unit := do
  r.section "multibase" "multiformats/multibase tests/*.csv"

  for (file, input) in
      [("multibase-basic.json", "yes mani !"),
       ("multibase-leading-zero.json", "\x00yes mani !"),
       ("multibase-two-leading-zeros.json", "\x00\x00yes mani !")] do
    let j ← loadJson file
    let bytes := Bytes.ofString input
    for c in (← jArr file j "cases") do
      let kind ← jStr file c "encoding"
      let want ← jStr file c "expected"
      let name := s!"multibase {kind} ({file})"
      match mbKind? kind with
      | none => r.skip name  -- header row ("encoding") or unsupported base
      | some base =>
          r.check s!"{name} encode" (Multibase.encode base bytes == want)
          match Multibase.decode? want with
          | some (b, out) =>
              r.check s!"{name} decode base" (b == base)
              r.check s!"{name} decode bytes" (out == bytes)
          | none => r.check s!"{name} decode" false

  -- Case-insensitivity file: decode-only (values are non-canonical).
  let j ← loadJson "multibase-case-insensitivity.json"
  let bytes := Bytes.ofString "hello world"
  for c in (← jArr "multibase-case-insensitivity.json" j "cases") do
    let kind ← jStr "multibase-case-insensitivity.json" c "encoding"
    let val ← jStr "multibase-case-insensitivity.json" c "expected"
    let name := s!"multibase case-insensitive decode {kind}"
    match mbKind? kind with
    | none => r.skip name
    | some base =>
        match Multibase.decode? val with
        | some (b, out) =>
            r.check s!"{name} bytes" (out == bytes)
            r.check s!"{name} base" (b == base)
        | none => r.check name false

  -- decode rejects unknown prefixes and bad digits
  r.check "multibase rejects unknown prefix" (Multibase.decode? "?abc" == none)
  r.check "multibase rejects empty" (Multibase.decode? "" == none)
  r.check "multibase rejects bad base32 digit" (Multibase.decode? "b1n1" == none)
  r.check "multibase rejects odd hex" (Multibase.decode? "fabc" == none)
  -- padded forms are canonical: missing or wrong '=' padding is rejected
  -- (a padded-form body whose length is already a multiple of the group
  -- size legitimately needs no '='; a non-multiple length does)
  r.check "multibase base32pad requires padding"
    (Multibase.decode? "cnbswy3dpeB3W64TMMQ" == none)
  r.check "multibase base32pad rejects wrong padding"
    (Multibase.decode? "cnbswy3dpeB3W64TMMQ=" == none)
  r.check "multibase base64pad requires padding"
    (Multibase.decode? "MeWVzIG1hbmkgIQ" == none)
  r.check "multibase base64pad accepts canonical padding"
    ((Multibase.decode? "MeWVzIG1hbmkgIQ==").isSome)

end Tests
