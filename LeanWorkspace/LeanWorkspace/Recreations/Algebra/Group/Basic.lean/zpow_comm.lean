import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem zpow_comm (a : α) (m n : ℤ) : (a ^ m) ^ n = (a ^ n) ^ m := by rw [← zpow_mul, zpow_mul']

