import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_mul_comm : a / b * c = c / b * a := by simp

