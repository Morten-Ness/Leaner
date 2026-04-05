import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem Ring.not_isUnit_iff_inverse_eq_zero [Nontrivial M₀] {x : M₀} : ¬ IsUnit x ↔ x⁻¹ʳ = 0 := by
  grind

