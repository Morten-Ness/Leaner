import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_natCast_sub_one (a : G) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa [div_eq_mul_inv] using zpow_sub a n 1

