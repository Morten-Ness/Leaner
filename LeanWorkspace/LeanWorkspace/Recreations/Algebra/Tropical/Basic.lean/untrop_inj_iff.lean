import Mathlib

variable (R : Type u)

theorem untrop_inj_iff (x y : Tropical R) : Tropical.untrop x = Tropical.untrop y ↔ x = y := Iff.rfl

