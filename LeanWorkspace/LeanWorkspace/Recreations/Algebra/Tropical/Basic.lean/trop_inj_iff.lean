import Mathlib

variable (R : Type u)

theorem trop_inj_iff (x y : R) : Tropical.trop x = Tropical.trop y ↔ x = y := Iff.rfl

