import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp

