import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp

