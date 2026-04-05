import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_zero : (0 : M₀)⁻¹ʳ = 0 := by
  nontriviality
  exact Ring.inverse_non_unit _ not_isUnit_zero

