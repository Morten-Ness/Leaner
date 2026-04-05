import Mathlib

variable (R : Type u)

theorem trop_coe_ne_zero (x : R) : Tropical.trop (x : WithTop R) ≠ 0 := nofun

