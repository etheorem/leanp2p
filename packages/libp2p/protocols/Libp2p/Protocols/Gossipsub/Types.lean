import Libp2p.Identity

/-!
# Gossipsub shared types

The types that every gossipsub module reads: the topic and message ids,
the published message, the score value and its thresholds, and the time
unit. The RPC codec, the scoring function, the caches, the signing
policy, and the router core all build on these, so they live in one
module that imports nothing else of gossipsub.

A score is an `Int` in fixed point: `scoreScale` units make 1.0 of the
pubsub spec. The spec states scores as float64. Fixed point keeps the
arithmetic exact, so `omega` can close the score theorems.

Time enters the router as data. `Millis` is the time of an `Event.tick`
in milliseconds. No gossipsub module reads a clock.
-/

set_option autoImplicit false

namespace Libp2p.Protocols.Gossipsub

open Libp2p.Identity

/-- A topic, by its name. -/
structure TopicId where
  name : String
  deriving DecidableEq, BEq, Hashable, Repr

/-- A message id: the bytes the message id function returns. -/
structure MessageId where
  bytes : List Nat
  deriving DecidableEq, BEq, Hashable, Repr

/-- A published message, with the fields of the pubsub spec. Each
optional field of the protobuf is an `Option`, so an absent field and
an empty field stay apart. -/
structure Message where
  /-- The author's peer id bytes. -/
  «from» : Option (List Nat)
  /-- The payload. -/
  data : Option (List Nat)
  /-- The sequence number bytes. -/
  seqno : Option (List Nat)
  /-- The topic, a required field. -/
  topic : TopicId
  /-- The signature over the message. -/
  signature : Option (List Nat)
  /-- The author's public key, when the peer id does not inline it. -/
  key : Option (List Nat)
  deriving DecidableEq, BEq, Repr

/-- A peer score, in fixed point: `scoreScale` units per 1.0. -/
abbrev Score := Int

/-- The fixed-point scale of `Score`. -/
def scoreScale : Nat := 1000

/-- The score thresholds of gossipsub v1.1. The router compares a peer's
score with them. The spec leaves the values to the application. -/
structure Thresholds where
  /-- Below this score, the router emits no gossip to the peer and
  ignores its gossip. -/
  gossipThreshold : Score
  /-- Below this score, the router does not publish to the peer. -/
  publishThreshold : Score
  /-- Below this score, the router ignores every RPC from the peer. -/
  graylistThreshold : Score
  /-- At or above this score, the router accepts peer exchange from
  the peer's prune. -/
  acceptPXThreshold : Score
  /-- Below this median mesh score, the router grafts opportunistically. -/
  opportunisticGraftThreshold : Score
  deriving DecidableEq, Repr

/-- A point in time, in milliseconds. -/
abbrev Millis := Nat

/-- The validated peer id of the identity package. -/
abbrev Peer := Libp2p.Identity.PeerId

end Libp2p.Protocols.Gossipsub
