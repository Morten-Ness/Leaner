import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_one' (h : u * v = 1) : u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  have h' : v * u = 1 := mul_comm u v ▸ h
  obtain rfl | rfl := Int.eq_one_or_neg_one_of_mul_eq_one h <;>
      obtain rfl | rfl := Int.eq_one_or_neg_one_of_mul_eq_one h' <;> tauto

