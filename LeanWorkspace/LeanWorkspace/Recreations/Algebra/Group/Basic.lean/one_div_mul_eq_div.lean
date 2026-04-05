import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem one_div_mul_eq_div : 1 / a * b = b / a := by simp

