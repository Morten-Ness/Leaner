import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp

