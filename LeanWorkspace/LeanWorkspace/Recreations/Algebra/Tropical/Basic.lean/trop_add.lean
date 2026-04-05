import Mathlib

variable (R : Type u)

theorem trop_add [Add R] (x y : R) : Tropical.trop (x + y) = Tropical.trop x * Tropical.trop y := rfl

