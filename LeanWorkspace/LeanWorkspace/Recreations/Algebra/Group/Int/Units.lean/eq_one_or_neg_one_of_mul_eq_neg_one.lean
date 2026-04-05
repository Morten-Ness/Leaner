import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_neg_one (h : u * v = -1) : u = 1 ∨ u = -1 := Or.elim (Int.eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1

