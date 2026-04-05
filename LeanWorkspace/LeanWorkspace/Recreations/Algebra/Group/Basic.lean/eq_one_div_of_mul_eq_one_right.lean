import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]

