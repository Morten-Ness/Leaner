import Mathlib

theorem negOnePow_succ (n : ℤ) : (n + 1).negOnePow = -n.negOnePow := by
  rw [Int.negOnePow_add, Int.negOnePow_one, mul_neg, mul_one]

