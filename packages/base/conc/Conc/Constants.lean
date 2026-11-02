/-!
# The constants of `conc`

The one constants module of the package (ARCHITECTURE §3.8).
-/

set_option autoImplicit false

namespace Conc

/-- The number of task errors that a `TaskSet` keeps for `joinAll`. The
bound stops a long series of failing tasks from growing the set without
end. No spec fixes the value. 16 is a choice, large enough to show a
pattern in a log. `joinAll` counts every failure, kept or not. -/
def maxTaskErrors : Nat := 16

end Conc
