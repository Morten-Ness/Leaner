import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp

