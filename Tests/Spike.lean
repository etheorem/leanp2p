import Tests.Support

/-!
# Spike unit tests

Our own unit tests from the original spike, kept as a suite. No upstream
mirror: these pin invariants of the internal models (frame codec, negotiation
core, peer id shape, byte helpers) between upstream vector suites.
-/

open LeanP2P Tests

namespace Tests

def Spike.run (r : Runner) : IO Unit := do
  r.section "spike" "(internal unit tests; no upstream mirror)"

  -- Frame codec
  let f : Framing.Frame := { sid := 3, payload := [104, 105] }
  r.check "frame roundtrip" (Framing.decode? (Framing.encode f) == some (f, []))
  r.check "frame trailing" (Framing.decode? (Framing.encode f ++ [1]) == some (f, [1]))
  r.check "frame short" (Framing.decode? [1, 2, 3] == none)

  -- Negotiation core
  r.check "multiselect choose" (Multiselect.choose ["/a/1", "/b/1"] ["/b/1", "/c/1"] == some "/b/1")
  r.check "multiselect priority" (Multiselect.choose ["/b/1", "/a/1"] ["/a/1", "/b/1"] == some "/b/1")
  r.check "multiselect none" (Multiselect.choose ["/a/1"] ["/b/1"] == none)

  -- PeerId is a sha2-256 multihash of the key bytes (libp2p shape; identity
  -- inlining arrives in phase 2 step 13)
  r.check "peerid deterministic"
    (PeerId.derive (PubKey.ofSeed "x") == PeerId.derive (PubKey.ofSeed "x"))
  r.check "peerid distinct"
    (PeerId.derive (PubKey.ofSeed "x") != PeerId.derive (PubKey.ofSeed "y"))
  r.check "peerid multihash shape"
    (PeerId.derive (PubKey.ofSeed "x") ==
      { bytes := Bytes.ofNatList (Multihash.sha256 (Bytes.toNatList (Bytes.ofString "x"))) })

  -- Byte helpers
  r.check "hex roundtrip"
    (Bytes.ofHex? (Bytes.toHex (Bytes.ofString "libp2p")) == some (Bytes.ofString "libp2p"))
  r.check "xor involution"
    (Bytes.xorWith "k".toUTF8 (Bytes.xorWith "k".toUTF8 (Bytes.ofString "abc")) == Bytes.ofString "abc")

end Tests
