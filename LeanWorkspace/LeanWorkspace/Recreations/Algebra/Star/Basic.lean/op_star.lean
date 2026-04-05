import Mathlib

open scoped Ring

variable {R : Type u}

theorem op_star [Star R] (r : R) : op (star r) = star (op r) := rfl

