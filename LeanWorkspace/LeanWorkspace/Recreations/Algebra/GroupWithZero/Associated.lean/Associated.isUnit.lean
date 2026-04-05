import Mathlib

variable {M : Type*}

theorem Associated.isUnit [Monoid M] {a b : M} (h : a ~ᵤ b) : IsUnit a → IsUnit b := let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ => ⟨v * u, by simp [hv, Associated.symm hu]⟩

