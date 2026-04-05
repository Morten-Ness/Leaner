import Mathlib

theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z := by
  rw [normalize_apply, Int.normUnit_eq, if_pos h, Units.val_one, mul_one]

