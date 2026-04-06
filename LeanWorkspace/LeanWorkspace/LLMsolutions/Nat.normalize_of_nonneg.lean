FAIL
import Mathlib

theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z := by
  rw [normalize]
  by_cases hz : z = 0
  · simp [hz]
  · have hz' : 0 < z := lt_of_le_of_ne h hz
    have hu : normUnit z = 1 := by
      rw [Int.normUnit_eq]
      simp [hz', le_of_lt hz']
    simp [hu]
