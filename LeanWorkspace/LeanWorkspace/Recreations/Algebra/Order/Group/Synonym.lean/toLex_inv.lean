import Mathlib

variable {α β : Type*}

theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ := rfl

