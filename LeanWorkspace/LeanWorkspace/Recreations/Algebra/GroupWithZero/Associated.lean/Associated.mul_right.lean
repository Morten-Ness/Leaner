import Mathlib

variable {M : Type*}

theorem Associated.mul_right [CommMonoid M] {a b : M} (h : a ~ᵤ b) (c : M) : a * c ~ᵤ b * c := by
  obtain ⟨d, Associated.rfl⟩ := h; exact ⟨d, mul_right_comm _ _ _⟩

