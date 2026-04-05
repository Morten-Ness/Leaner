import Mathlib

variable {M : Type*}

theorem Associated.dvd' [Monoid M] {a b : M} (h : a ~ᵤ b) : b ∣ a := Associated.symm h.dvd

