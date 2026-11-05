import Libp2p.Security.Constants
import Libp2p.Security.Handshake
import Libp2p.Security.Mock.Core

/-!
# Libp2p.Security

Noise `XX` as a `SecurityProtocol` value (ARCHITECTURE §4.9).

The package is staged as unit W5.3 of `docs/PLAN.md`:

- `Constants` — the protocol id, the handshake name, and the wire caps the
  framing derives from.
- `Handshake` — the pure state machine: symmetric state, the three messages,
  and `step`, which returns the bytes to write and the transport keys.
- `Mock/Core` — the core surface (`Role`, `PeerId`, `Error`, `SecureConn`)
  until unit W3.1 lands the real core package. It is the only mock here.

Not yet in this tree, and deliberately listed rather than stubbed: the payload
(peer-id binding and identity signature, 8 KiB cap), the transport (length
prefix, 65535-byte frames, per-direction nonce), and the vector tests ported
from the spike branch. See the PR body for the order.
-/
