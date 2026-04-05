import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, inv_pow]
  | .negSucc n => by rw [zpow_negSucc, zpow_negSucc, inv_pow]
