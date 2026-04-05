import Mathlib

open scoped Ring

variable {R : Type u}

theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) := rfl

