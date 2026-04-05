import Mathlib

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {a : M₀} {n : ℕ}

theorem zero_pow_eq_one₀ [Nontrivial M₀] : (0 : M₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_pow_eq, one_ne_zero.ite_eq_left_iff]

