import Multiformats.Tables
import Multiformats.Constants
import Multiformats.Error
import Multiformats.Base58
import Multiformats.Multibase
import Multiformats.Multihash
import Multiformats.Cid
import Multiformats.ComponentWire
import Multiformats.SequenceWire
import Multiformats.SequenceOps
import Multiformats.Multiaddr.Ip
import Multiformats.Multiaddr.Percent
import Multiformats.Multiaddr.Value
import Multiformats.Multiaddr.Segments
import Multiformats.Multiaddr.Core
import Multiformats.Multiaddr.Text
import Multiformats.Multiaddr.Binary
import Multiformats.Multiaddr.Ops
import Multiformats.Multiaddr

/-!
# Multiformats

The encoding family of ARCHITECTURE §4.4. Registry tables are generated
from pinned inputs. The checked wire models own their bounds and codec
laws; the byte paths are compared with those models by the shared suite.
-/
