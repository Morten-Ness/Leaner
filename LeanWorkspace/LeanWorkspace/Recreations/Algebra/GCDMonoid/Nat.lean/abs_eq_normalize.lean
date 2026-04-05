import Mathlib

theorem abs_eq_normalize (z : ℤ) : |z| = normalize z := by
  cases le_total 0 z <;>
  simp [abs_of_nonneg, abs_of_nonpos, Int.normalize_of_nonneg, Int.normalize_of_nonpos, *]

