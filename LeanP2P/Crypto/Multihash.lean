import LeanP2P.Crypto.Sha256
import LeanP2P.Crypto.Sha1
import LeanP2P.Net.Varint
/-!
# Multihash

`<varint code><varint digest length><digest>` per multiformats/multihash.
Decoding is strict (VECTOR_TEST_PLAN.md phase 1 step 7): the code must be in
the function table, the digest must have exactly the declared length, and a
standalone decode must consume the whole input. Peer-id validation
(identity / sha2-256 only, sha2-256 digests exactly 32 bytes) follows
go-multiaddr's `p2pVal` and the peer-ids spec.
-/

namespace LeanP2P.Multihash

/-- A decoded multihash: function code and digest bytes. -/
structure Multihash where
  code : Nat
  digest : List Nat
deriving Repr, BEq

/-- The function table (code, name) we recognise when decoding: the
multicodec hash block. Certhash values may use any of these (Go accepts
any registry code). -/
def codeTable : List (Nat × String) :=
  [(0x00, "identity"), (0x11, "sha1"), (0x12, "sha2-256"),
   (0x13, "sha2-512"), (0x14, "sha3-512"), (0x15, "sha3-384"),
   (0x16, "sha3-256"), (0x17, "sha3-224"), (0x18, "shake-128"),
   (0x19, "shake-256"), (0x1a, "keccak-224"), (0x1b, "keccak-256"),
   (0x1c, "keccak-384"), (0x1d, "keccak-512"), (0x56, "dbl-sha2-256"),
   (0xd4, "md4"), (0xd5, "md5"),
   (0xb201, "blake2b-8"), (0xb202, "blake2b-16"), (0xb203, "blake2b-24"),
   (0xb204, "blake2b-32"), (0xb205, "blake2b-40"), (0xb206, "blake2b-48"),
   (0xb207, "blake2b-56"), (0xb208, "blake2b-64"), (0xb209, "blake2b-72"),
   (0xb20a, "blake2b-80"), (0xb20b, "blake2b-88"), (0xb20c, "blake2b-96"),
   (0xb20d, "blake2b-104"), (0xb20e, "blake2b-112"), (0xb20f, "blake2b-120"),
   (0xb210, "blake2b-128"), (0xb211, "blake2b-136"), (0xb212, "blake2b-144"),
   (0xb213, "blake2b-152"), (0xb214, "blake2b-160"), (0xb215, "blake2b-168"),
   (0xb216, "blake2b-176"), (0xb217, "blake2b-184"), (0xb218, "blake2b-192"),
   (0xb219, "blake2b-200"), (0xb21a, "blake2b-208"), (0xb21b, "blake2b-216"),
   (0xb21c, "blake2b-224"), (0xb21d, "blake2b-232"), (0xb21e, "blake2b-240"),
   (0xb21f, "blake2b-248"), (0xb220, "blake2b-256"), (0xb221, "blake2b-264"),
   (0xb222, "blake2b-272"), (0xb223, "blake2b-280"), (0xb224, "blake2b-288"),
   (0xb225, "blake2b-296"), (0xb226, "blake2b-304"), (0xb227, "blake2b-312"),
   (0xb228, "blake2b-320"), (0xb229, "blake2b-328"), (0xb22a, "blake2b-336"),
   (0xb22b, "blake2b-344"), (0xb22c, "blake2b-352"), (0xb22d, "blake2b-360"),
   (0xb22e, "blake2b-368"), (0xb22f, "blake2b-376"), (0xb238, "blake2b-384"),
   (0xb240, "blake2b-440"), (0xb248, "blake2b-480"), (0xb250, "blake2b-512"),
   (0xb251, "blake2s-8"), (0xb252, "blake2s-16"), (0xb253, "blake2s-24"),
   (0xb254, "blake2s-32"), (0xb255, "blake2s-40"), (0xb256, "blake2s-48"),
   (0xb257, "blake2s-56"), (0xb258, "blake2s-64"), (0xb259, "blake2s-72"),
   (0xb25a, "blake2s-80"), (0xb25b, "blake2s-88"), (0xb25c, "blake2s-96"),
   (0xb25d, "blake2s-104"), (0xb25e, "blake2s-112"), (0xb25f, "blake2s-120"),
   (0xb260, "blake2s-128")]

def codeName (code : Nat) : Option String := codeTable.lookup code

def codeIdentity : Nat := 0x00
def codeSha1 : Nat := 0x11
def codeSha256 : Nat := 0x12

/-- Wire bytes of a multihash. -/
def encode (mh : Multihash) : List Nat :=
  Varint.encode mh.code ++ Varint.encode mh.digest.length ++ mh.digest

/-- Strict decode at the head of `bs`: consumes exactly the multihash and
returns the rest. -/
def decodeAt? (bs : List Nat) : Option (Multihash × List Nat) := do
  let (code, rest) ← Varint.decode? bs
  if ← pure (codeTable.any (fun e => e.1 == code)) then
    pure ()
  else failure
  let (len, rest) ← Varint.decode? rest
  if rest.length < len then none
  else some ({ code := code, digest := rest.take len }, rest.drop len)

/-- Strict standalone decode: consumes the whole input. -/
def decode? (bs : List Nat) : Option Multihash := do
  let (mh, rest) ← decodeAt? bs
  if rest = [] then some mh else none

/-- Peer-id multihash rule (peer-ids spec / go-multiaddr `p2pVal`): the
function must be identity or sha2-256, and sha2-256 digests are exactly
32 bytes. -/
def validPeer (mh : Multihash) : Bool :=
  (mh.code = codeIdentity ∨ mh.code = codeSha256) ∧
  (mh.code = codeSha256 → mh.digest.length = 32)

/-- sha2-256 multihash: `12 20 <32 bytes>` — the libp2p PeerId shape for
non-inlined keys. -/
def sha256 (bs : List Nat) : List Nat :=
  encode { code := codeSha256, digest := Sha256.digest bs }

/-- sha1 multihash (multihash README vector only). -/
def sha1 (bs : List Nat) : List Nat :=
  encode { code := codeSha1, digest := Sha1.digest bs }

/-- identity multihash: `00 <len> <bytes>` (digest equals the value). -/
def identity (bs : List Nat) : List Nat :=
  encode { code := codeIdentity, digest := bs }

end LeanP2P.Multihash
