import Mathlib

variable {α β : Type*}

theorem ofColex_inv [Inv α] (a : Colex α) : ofColex a⁻¹ = (ofColex a)⁻¹ := rfl

