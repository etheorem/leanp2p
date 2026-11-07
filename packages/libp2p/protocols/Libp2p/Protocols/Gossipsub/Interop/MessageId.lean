import Libp2p.Protocols.Gossipsub.Core

/-!
# GossipSub interop message ids

This module implements specification section 6. The harness reads the first
8 payload bytes as one big endian unsigned integer and prints base ten.
A short payload gets zero bytes appended on the right. This gives a total
function and matches the byte-position rule for every available byte.

The core stores the same padded eight bytes in MessageId. A caller can use
coreMsgId in Core.Params.msgId without changing the core state machine.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub.Interop

open Libp2p.Protocols.Gossipsub

/-- Pad a payload on the right so the id always has eight input bytes. -/
def paddedPayload (payload : List Nat) : List Nat :=
  let headBytes := payload.take 8; headBytes ++ List.replicate (8 - headBytes.length) 0

/-- Read up to eight bytes as a big endian natural number. -/
def readBigEndian (bytes : List Nat) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte % 256) 0

/-- Read the message id as an unsigned 64 bit value. -/
def messageIdNumber (payload : List Nat) : UInt64 :=
  UInt64.ofNat (readBigEndian (paddedPayload payload))

/-- Format the message id as an unsigned base ten string. -/
def messageIdString (payload : List Nat) : String :=
  (messageIdNumber payload).toNat |> Nat.repr

/-- Adapt a gossipsub message to the harness message id rule. -/
def coreMsgId (message : Message) : MessageId :=
  ⟨paddedPayload ((message.data).getD [])⟩

/-- The function value for Core.Params.msgId. -/
def msgIdFn : Sign.MsgIdFn := coreMsgId

end Libp2p.Protocols.Gossipsub.Interop
