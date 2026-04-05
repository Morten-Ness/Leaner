import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_zero_right (a : R) : gcd a 0 = a := by
  rw [gcd]
  split_ifs with h <;> simp only [h, EuclideanDomain.zero_mod, gcd_zero_left]

