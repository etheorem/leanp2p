import Bytes

/-! # Errors shared by the nested multiformats decoders. -/

set_option autoImplicit false

namespace Multiformats

/-- Each wire boundary retains its failure family until the shared codec seam. -/
inductive Error where
  | framing (reason : Bytes.DecodeError)
  | unknownHash
  | badDigest
  | unknownBase
  | badBaseValue
  | badCid
  | unknownProtocol
  | badValue
  | badAddress
  | overCap
  deriving DecidableEq, BEq, Repr, Hashable

/-- A structural wire violation is malformed; incomplete framing can grow. -/
def Error.toDecodeError : Error → Bytes.DecodeError
  | .framing reason => reason
  | _ => .malformed

end Multiformats
