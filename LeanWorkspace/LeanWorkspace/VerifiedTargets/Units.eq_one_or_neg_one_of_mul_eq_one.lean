import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_one (h : u * v = 1) : u = 1 ∨ u = -1 := Int.isUnit_iff.1 (.of_mul_eq_one v h)

