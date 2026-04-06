FAIL
import Mathlib

theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z := by
  constructor
  · intro h
    by_cases hz : 0 ≤ z
    · exact hz
    · have hzlt : z < 0 := lt_of_not_ge hz
      have hnorm : normalize z = -z := by
        simp [normalize, hzlt, le_of_lt hzlt]
      rw [hnorm] at h
      linarith
  · intro hz
    simp [normalize, hz]
