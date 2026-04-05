import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

