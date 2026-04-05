import Mathlib

variable {α : Type u}

theorem coe_inv [Inv α] (a : α) : ((a⁻¹ : α) : WithOne α) = (a : WithOne α)⁻¹ := rfl

