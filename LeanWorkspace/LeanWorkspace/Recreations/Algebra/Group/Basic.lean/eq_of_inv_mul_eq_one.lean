import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

