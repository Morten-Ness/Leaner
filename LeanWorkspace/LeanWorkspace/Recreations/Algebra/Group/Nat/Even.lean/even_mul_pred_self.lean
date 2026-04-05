import Mathlib

variable {m n : ℕ}

theorem even_mul_pred_self (n : ℕ) : Even (n * (n - 1)) := by grind

