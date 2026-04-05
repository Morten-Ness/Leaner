import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

