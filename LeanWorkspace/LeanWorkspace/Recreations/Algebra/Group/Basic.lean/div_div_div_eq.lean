import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp

