import Mathlib

theorem abs_sign_of_ne_zero {z : ℤ} (hz : z ≠ 0) : |z.sign| = 1 := by
  rw [Int.abs_eq_natAbs, natAbs_sign_of_ne_zero hz, Int.ofNat_one]

