import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem Ring.isUnit_iff_inverse_mul_cancel (x : M₀) : IsUnit x ↔ x⁻¹ʳ * x = 1 := by
  nontriviality M₀
  refine ⟨Ring.inverse_mul_cancel x, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_inverse_mul_cancel => IsUnit x, x⁻¹ʳ

