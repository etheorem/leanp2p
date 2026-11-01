/-!
# `OnceRef`: the atomic cell

Shared state changes in one step (ARCHITECTURE §4.1, rule 3). A get and
then a set on a bare `IO.Ref` loses an update when two tasks interleave
between them. `OnceRef.update` reads and writes in one atomic step:
`ST.Ref.modify` takes the value out of the cell, so a concurrent update
waits until this one puts the new value back.
-/

set_option autoImplicit false

namespace Conc

/-- A shared cell that changes only by atomic steps. -/
structure OnceRef (α : Type) where
  private ref : IO.Ref α

namespace OnceRef

variable {α β : Type}

/-- A cell that holds `a`. -/
def new (a : α) : BaseIO (OnceRef α) :=
  return ⟨← IO.mkRef a⟩

/-- The current value. -/
def get (r : OnceRef α) : BaseIO α :=
  r.ref.get

/-- Replace the value. A value that depends on the old one goes through
`update` instead.

A bare `IO.Ref.set` can lose its value here. `IO.Ref.get` takes the value
out of a shared cell and puts it back, and a `set` between those two
steps is overwritten by the old value. `modify` waits for the cell to
hold a value, so the write goes through it. -/
def set (r : OnceRef α) (a : α) : BaseIO Unit :=
  r.ref.modify fun _ => a

/-- Apply `f` to the value in one atomic step. -/
def update (r : OnceRef α) (f : α → α) : BaseIO Unit :=
  r.ref.modify f

/-- Apply `f` in one atomic step, and return its first component. -/
def updateGet (r : OnceRef α) (f : α → β × α) : BaseIO β :=
  r.ref.modifyGet f

end OnceRef

end Conc
