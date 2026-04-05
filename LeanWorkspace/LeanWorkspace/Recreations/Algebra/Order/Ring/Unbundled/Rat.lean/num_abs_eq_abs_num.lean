import Mathlib

variable {a b c p q : ℚ}

theorem num_abs_eq_abs_num (q : ℚ) : |q|.num = |q.num| := by
  rw [Rat.abs_def']

