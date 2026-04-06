FAIL
import Mathlib

theorem abs_eq_normalize (z : ℤ) : |z| = normalize z := by
  rcases le_or_lt 0 z with hz | hz
  · rw [Int.natAbs_of_nonneg hz, Int.abs_of_nonneg hz, normalize, Int.units_eq_one_or]
    · simp
    · exact hz
  · rw [Int.abs_of_neg hz, normalize]
    have hzu : normUnit z = -1 := by
      rw [Int.units_eq_one_or]
      · simp
      · exact le_of_lt hz
    rw [hzu]
    ring
