import Mathlib

variable {M : Type*}

theorem Associated.dvd_iff_dvd_right [Monoid M] {a b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c := let ⟨_, hu⟩ := h
  hu ▸ Units.Associated.symm dvd_mul_right

