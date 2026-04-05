import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem one_zpow : ∀ n : ℤ, (1 : α) ^ n = 1
  | (n : ℕ) => by rw [zpow_natCast, one_pow]
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]
