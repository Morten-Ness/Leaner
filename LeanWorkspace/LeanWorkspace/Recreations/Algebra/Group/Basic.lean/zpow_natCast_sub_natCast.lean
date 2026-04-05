import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_natCast_sub_natCast (a : G) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a m n

