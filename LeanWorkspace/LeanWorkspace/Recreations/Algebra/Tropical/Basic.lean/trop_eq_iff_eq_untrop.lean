import Mathlib

variable (R : Type u)

theorem trop_eq_iff_eq_untrop {x : R} {y} : Tropical.trop x = y ↔ x = Tropical.untrop y := Tropical.tropEquiv.apply_eq_iff_eq_symm_apply

