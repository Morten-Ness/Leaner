import Mathlib

variable (R : Type u)

theorem untrop_trop (x : R) : Tropical.untrop (Tropical.trop x) = x := rfl

attribute [irreducible] Tropical

