import Mathlib

theorem negOnePow_mul_self (n : ℤ) : (n * n).negOnePow = n.negOnePow := by
  simpa [mul_sub, Int.negOnePow_eq_iff] using n.even_mul_pred_self

