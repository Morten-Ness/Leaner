import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem Ring.isUnit_iff_mul_inverse_cancel {x : M₀} : IsUnit x ↔ x * x⁻¹ʳ = 1 := by
  nontriviality M₀
  refine ⟨Ring.mul_inverse_cancel _, ?_⟩
  contrapose
  simp +contextual [not_isUnit_iff_inverse_eq_zero]

grind_pattern Ring.isUnit_iff_mul_inverse_cancel => IsUnit x, x⁻¹ʳ

