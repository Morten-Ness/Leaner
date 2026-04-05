import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp

