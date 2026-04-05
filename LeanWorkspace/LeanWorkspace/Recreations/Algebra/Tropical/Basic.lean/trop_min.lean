import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem trop_min (x y : R) : Tropical.trop (min x y) = Tropical.trop x + Tropical.trop y := rfl

