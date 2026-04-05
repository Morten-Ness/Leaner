import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a := by
  rw [gcd]
  split_ifs with h <;> [simp only [h, mod_zero, EuclideanDomain.gcd_zero_right]; rfl]

