import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem Ring.inverse_inverse_inverse {a : M₀} : a⁻¹ʳ⁻¹ʳ⁻¹ʳ = a⁻¹ʳ := by
  nontriviality M₀
  by_cases h : IsUnit a
  · rw [Ring.inverse_inverse h]
  · simp [Ring.not_isUnit_iff_inverse_eq_zero.mp h]

