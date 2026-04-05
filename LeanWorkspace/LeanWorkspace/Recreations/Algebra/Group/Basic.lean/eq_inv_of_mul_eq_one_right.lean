import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ := (inv_eq_of_mul_eq_one_right h).symm

