FAIL
import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) := by
  simpa [Commute.mul_right_cancel_iff] using (mul_zpow a m n).symm
