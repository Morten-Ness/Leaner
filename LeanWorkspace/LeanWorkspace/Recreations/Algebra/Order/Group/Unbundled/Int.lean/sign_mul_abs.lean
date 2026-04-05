import Mathlib

theorem sign_mul_abs (a : ℤ) : sign a * |a| = a := by
  rw [Int.abs_eq_natAbs, sign_mul_natAbs a]

