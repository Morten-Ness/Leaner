import Mathlib

variable {a b c p q : ℚ}

theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.den := by
  grind [abs_of_nonpos, neg_def, Rat.num_nonneg, abs_of_nonneg, num_divInt_den]

