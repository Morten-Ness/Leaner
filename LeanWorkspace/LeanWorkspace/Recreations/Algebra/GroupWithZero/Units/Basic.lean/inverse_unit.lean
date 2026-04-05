import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ) := by
  rw [Ring.inverse, dif_pos u.isUnit, IsUnit.unit_of_val_units]

