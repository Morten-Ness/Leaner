import Mathlib

theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z := by
  by_cases! h : 0 ≤ z
  · exact h
  · rw [Int.normalize_of_nonpos h.le] at hz
    lia

