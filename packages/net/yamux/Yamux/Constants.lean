/-!
# Yamux constants

One home per fact (ARCHITECTURE §3.8). Every other module of the package
imports this one, so a number appears once and no second copy can drift
from it.

The values come from the hashicorp yamux specification and from the
hardening rules of `docs/ARCHITECTURE.md` §4.8. The package reads the
spec through `net/streams` and knows nothing above its own group (§2).
-/

namespace Yamux

/-- The frame header is 12 bytes: version (8 bits), type (8 bits), flags
(16 bits), stream id (32 bits), and length (32 bits). The layout is
stated once, in `Yamux/Header.lean`. -/
def headerSize : Nat := 12

/-- The receive window we grant every stream when it opens. The window
caps the data one peer can put in flight, and the session checks every
inbound data frame against it before it buffers a byte (ARCHITECTURE
§4.8, §5.1). -/
def initialWindow : Nat := 262144

/-- The largest data-frame payload the decoder accepts. A compliant peer
never sends more than the window we granted, so a longer frame is a
protocol error and not a frame to allocate. Without the cap, the 32-bit
length field would commit us to reading up to 4 GiB. -/
def maxDataFrame : Nat := initialWindow

/-- Cap on the queue that carries the frames we owe the peer. Beyond the
cap the session drops the frames a peer can re-derive or re-request, so
a hostile ping flood cannot grow the queue (PRINCIPLES 3.4). -/
def maxControlQueue : Nat := 1024

/-- Cap on streams a peer opened and we have not accepted. The yamux
spec makes the bound a SHOULD of 256; the package counts every
unrequested stream, which is stricter and bounds the session map
together with the retirement rule. -/
def maxInboundBacklog : Nat := 256

/-- The version this implementation speaks. The codec accepts no other
value, and a peer that sends another version is a protocol error. -/
def wireVersion : Nat := 0

/-- A window update may not move the send window past this bound. The
spec fixes the window as a 32-bit field, and the bound keeps the sum of
credit and the outstanding bytes inside the field width. -/
def maxWindow : Nat := 4294967295

end Yamux
