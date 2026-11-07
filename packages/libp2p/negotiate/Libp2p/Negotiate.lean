import Libp2p.Negotiate.Constants
import Libp2p.Negotiate.Message
import Libp2p.Negotiate.Step
import Libp2p.Negotiate.Upgrade

/-!
# Libp2p.Negotiate

The negotiate subpackage: multistream-select 1.0.0 and the upgrader
(ARCHITECTURE §4.9). One import line per public submodule. The root
names no Mock module directly. Its submodules still expose `Mock.Core`
until W5.2 lands. The identity field types name `Libp2p.Identity`.
-/
