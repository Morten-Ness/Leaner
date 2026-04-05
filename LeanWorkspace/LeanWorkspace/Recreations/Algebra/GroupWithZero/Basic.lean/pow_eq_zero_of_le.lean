import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem pow_eq_zero_of_le : ∀ {m n}, m ≤ n → a ^ m = 0 → a ^ n = 0
  | _, _, Nat.le.refl, ha => ha
  | _, _, Nat.le.step hmn, ha => by rw [pow_succ, pow_eq_zero_of_le hmn ha, zero_mul]
