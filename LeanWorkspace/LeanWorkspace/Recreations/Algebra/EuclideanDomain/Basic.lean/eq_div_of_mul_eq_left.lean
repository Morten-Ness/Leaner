import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  rw [← h, mul_div_cancel_right₀ _ hb]

