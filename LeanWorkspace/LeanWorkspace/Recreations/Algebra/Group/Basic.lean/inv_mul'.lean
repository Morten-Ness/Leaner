import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp

