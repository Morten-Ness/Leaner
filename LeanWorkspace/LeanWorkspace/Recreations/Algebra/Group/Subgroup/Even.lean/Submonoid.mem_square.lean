import Mathlib

variable {M : Type*} [CommMonoid M]

theorem mem_square {a : M} : a ∈ Submonoid.square M ↔ IsSquare a := Iff.rfl

