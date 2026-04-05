import Mathlib

variable (R : Type u)

theorem untrop_lt_iff [LT R] {x y : Tropical R} : Tropical.untrop x < Tropical.untrop y ↔ x < y := Iff.rfl

