import Mathlib

variable {M : Type*}

theorem Associated.dvd_iff_dvd_left [Monoid M] {a b c : M} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c := let ⟨_, hu⟩ := h
  hu ▸ Units.Associated.symm mul_right_dvd

