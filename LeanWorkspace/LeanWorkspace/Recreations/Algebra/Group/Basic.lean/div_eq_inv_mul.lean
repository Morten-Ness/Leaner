import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp

