import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp

