import Mathlib

variable {α β : Type*}

theorem toColex_inv [Inv α] (a : α) : toColex a⁻¹ = (toColex a)⁻¹ := rfl

