import Mathlib

theorem eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  lia

