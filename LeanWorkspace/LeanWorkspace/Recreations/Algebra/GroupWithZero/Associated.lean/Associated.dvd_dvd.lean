import Mathlib

variable {M : Type*}

theorem Associated.dvd_dvd [Monoid M] {a b : M} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a := ⟨h.dvd, Associated.symm h.dvd⟩

