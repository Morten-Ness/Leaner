import Mathlib

variable (R : Type u)

theorem untrop_eq_iff_eq_trop {x} {y : R} : Tropical.untrop x = y ↔ x = Tropical.trop y := Tropical.tropEquiv.symm.apply_eq_iff_eq_symm_apply

