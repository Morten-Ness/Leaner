import Mathlib

variable {S : Type*} [CommSemigroup S]

theorem mem_square {a : S} : a ∈ Subsemigroup.square S ↔ IsSquare a := Iff.rfl

