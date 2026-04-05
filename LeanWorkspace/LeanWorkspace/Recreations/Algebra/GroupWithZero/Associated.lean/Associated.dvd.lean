import Mathlib

variable {M : Type*}

theorem Associated.dvd [Monoid M] {a b : M} : a ~ᵤ b → a ∣ b := fun ⟨u, hu⟩ =>
  ⟨u, Associated.symm hu⟩

