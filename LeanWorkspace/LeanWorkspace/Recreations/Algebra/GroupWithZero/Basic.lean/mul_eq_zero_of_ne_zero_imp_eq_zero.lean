import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 := by
  have : Decidable (a = 0) := Classical.propDecidable (a = 0)
  exact if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

