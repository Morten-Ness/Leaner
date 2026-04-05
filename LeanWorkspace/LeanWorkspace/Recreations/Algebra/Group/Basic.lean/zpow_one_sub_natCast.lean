import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_one_sub_natCast (a : G) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a 1 n

