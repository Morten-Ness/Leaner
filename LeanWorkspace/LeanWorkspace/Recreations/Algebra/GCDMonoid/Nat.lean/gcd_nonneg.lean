import Mathlib

theorem gcd_nonneg (i j : ℤ) : 0 ≤ GCDMonoid.gcd i j := by simp [← Int.coe_gcd]

