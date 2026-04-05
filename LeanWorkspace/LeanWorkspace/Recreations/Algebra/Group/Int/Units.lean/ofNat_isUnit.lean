import Mathlib

variable {u v : ℤ}

theorem ofNat_isUnit {n : ℕ} : IsUnit (n : ℤ) ↔ IsUnit n := by simp [Int.isUnit_iff_natAbs_eq]

