import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem untrop_add (x y : Tropical R) : Tropical.untrop (x + y) = min (Tropical.untrop x) (Tropical.untrop y) := rfl

