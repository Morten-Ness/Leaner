import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_eq_zpow_emod {x : G} (m : ℤ) {n : ℤ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) := calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_mul_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]

