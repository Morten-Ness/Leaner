import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * x⁻¹ʳ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [Ring.inverse_unit, Units.mul_inv]

