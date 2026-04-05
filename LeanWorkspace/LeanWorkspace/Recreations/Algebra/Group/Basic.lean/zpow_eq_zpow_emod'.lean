import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_eq_zpow_emod' {x : G} (m : ℤ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : ℤ)) := zpow_eq_zpow_emod m (by simpa)

