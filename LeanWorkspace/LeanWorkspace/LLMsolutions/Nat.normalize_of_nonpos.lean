FAIL
import Mathlib

theorem normalize_of_nonpos {z : ℤ} (h : z ≤ 0) : normalize z = -z := by
  cases' Int.eq_nat_or_neg z with n hn n hn
  · subst hn
    have : n = 0 := by
      have hn' : (n : ℤ) ≤ 0 := by simpa using h
      exact Int.ofNat_eq_zero.mp (le_antisymm hn' (Int.ofNat_nonneg n))
    subst this
    simp
  · subst hn
    simp
