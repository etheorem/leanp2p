import Libp2p.Protocols.Gossipsub.Interop.Address
import Libp2p.Protocols.Gossipsub.Interop.Hosts
import Libp2p.Protocols.Gossipsub.Interop.MessageId
import Libp2p.Protocols.Gossipsub.Interop.Record
import Libp2p.Protocols.Gossipsub.Interop.Schedule
import Libp2p.Protocols.Gossipsub.Interop.Script

/-!
# GossipSub interop pure core

This root re-exports the pure adapter parts. The parser, hosts resolver, virtual
schedule, record encoder, address helpers, and message id functions perform no
network IO. Only the hosts-file edge reads the filesystem.
-/
