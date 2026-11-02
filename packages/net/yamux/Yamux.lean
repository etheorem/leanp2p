import Yamux.Constants
import Yamux.Sets
import Yamux.Header
import Yamux.Error
import Yamux.Frame
import Yamux.Core
import Yamux.Sink

/-!
# Yamux

The yamux session, the interop muxer (ARCHITECTURE §4.8). The package
holds the 12-byte header codec, the stream state machine, and flow
control, over a `Connection` of `net/streams`. It knows nothing above
its own group: the `Muxer` value that assigns `/yamux/1.0.0` lives in the
protocol stack (W5.4).

The root module re-exports the public submodules.
-/
