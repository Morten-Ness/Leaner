import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_inverse {a : M₀} (h : IsUnit a) : a⁻¹ʳ⁻¹ʳ = a := by
  obtain ⟨u, rfl⟩ := h
  rw [Ring.inverse_unit, Ring.inverse_unit, inv_inv]

