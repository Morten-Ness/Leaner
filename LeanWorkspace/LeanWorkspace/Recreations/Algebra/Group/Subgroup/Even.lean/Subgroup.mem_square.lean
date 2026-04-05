import Mathlib

variable {G : Type*} [CommGroup G]

theorem mem_square {a : G} : a ∈ Subgroup.square G ↔ IsSquare a := Iff.rfl

