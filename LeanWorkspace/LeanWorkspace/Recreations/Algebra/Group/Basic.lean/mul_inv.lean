import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

