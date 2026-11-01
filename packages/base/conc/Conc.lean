import Conc.Constants
import Conc.Error
import Conc.Chan
import Conc.Select
import Conc.Pipe
import Conc.TaskSet
import Conc.OnceRef
import Conc.Deadline
import Conc.Clock
import Conc.Alarm
import Conc.Outcome

/-!
# Conc

The concurrency primitives of the stack (ARCHITECTURE §4.1): the
bounded `Chan`, `select`, `Pipe`, `TaskSet`, `OnceRef`,
`withinDeadline`, the `Clock` seam, `Alarm`, and `Outcome`. `Conc.Wrap`
is internal. Lean imports are transitive, so an importer of this root
can still see the `Wrap` and `Std` names. A caller names neither. The
package docs live under `docs/` beside this file.
-/
