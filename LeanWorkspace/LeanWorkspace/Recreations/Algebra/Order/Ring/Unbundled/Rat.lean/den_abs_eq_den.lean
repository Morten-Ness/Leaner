import Mathlib

variable {a b c p q : ℚ}

theorem den_abs_eq_den (q : ℚ) : |q|.den = q.den := by
  rw [Rat.abs_def']

