import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp

