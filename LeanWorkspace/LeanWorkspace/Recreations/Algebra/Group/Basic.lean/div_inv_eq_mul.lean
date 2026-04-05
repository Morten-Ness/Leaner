import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

