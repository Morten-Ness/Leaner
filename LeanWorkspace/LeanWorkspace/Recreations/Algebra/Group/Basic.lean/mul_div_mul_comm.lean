import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp

