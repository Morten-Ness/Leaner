import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]

