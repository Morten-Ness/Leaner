import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem untrop_max (x y : Tropical R) : Tropical.untrop (max x y) = max (Tropical.untrop x) (Tropical.untrop y) := rfl

