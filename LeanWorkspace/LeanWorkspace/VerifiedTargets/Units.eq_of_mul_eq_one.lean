import Mathlib

variable {u v : ℤ}

theorem eq_of_mul_eq_one (h : u * v = 1) : u = v := (Int.eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))

