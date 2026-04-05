import Mathlib

theorem lcm_nonneg (i j : ℤ) : 0 ≤ GCDMonoid.lcm i j := by simp [← Int.coe_lcm]

