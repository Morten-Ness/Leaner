import Mathlib

variable {α β : Type*}

theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ := rfl

