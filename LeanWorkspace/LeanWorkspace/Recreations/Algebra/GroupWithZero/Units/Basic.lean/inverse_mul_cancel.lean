import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻¹ʳ * x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [Ring.inverse_unit, Units.inv_mul]

