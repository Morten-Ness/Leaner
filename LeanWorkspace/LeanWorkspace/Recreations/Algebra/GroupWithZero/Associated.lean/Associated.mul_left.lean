import Mathlib

variable {M : Type*}

theorem Associated.mul_left [Monoid M] (a : M) {b c : M} (h : b ~ᵤ c) : a * b ~ᵤ a * c := by
  obtain ⟨d, Associated.rfl⟩ := h; exact ⟨d, mul_assoc _ _ _⟩

