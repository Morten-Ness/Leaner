import Mathlib

variable (R : Type u)

theorem zero_ne_trop_coe (x : R) : 0 ≠ (Tropical.trop x : Tropical (WithTop R)) := nofun

