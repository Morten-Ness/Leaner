import Mathlib

variable {M : Type*}

theorem Associated.of_eq [Monoid M] {a b : M} (h : a = b) : a ~ᵤ b := ⟨1, by rwa [Units.val_one, mul_one]⟩

