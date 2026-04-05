import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem mul_comm_div : a / b * c = a * (c / b) := by simp

