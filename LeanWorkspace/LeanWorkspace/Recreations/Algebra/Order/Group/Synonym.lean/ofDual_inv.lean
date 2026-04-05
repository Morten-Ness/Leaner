import Mathlib

variable {α β : Type*}

theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ := rfl

