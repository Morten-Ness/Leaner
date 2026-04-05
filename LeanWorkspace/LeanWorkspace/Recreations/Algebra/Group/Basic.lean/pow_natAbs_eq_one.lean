import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1 := by cases n <;> simp

