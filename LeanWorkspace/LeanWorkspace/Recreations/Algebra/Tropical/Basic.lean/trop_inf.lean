import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem trop_inf (x y : R) : Tropical.trop (x ⊓ y) = Tropical.trop x + Tropical.trop y := rfl

