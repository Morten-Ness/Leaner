import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem trop_add_def (x y : Tropical R) : x + y = Tropical.trop (min (Tropical.untrop x) (Tropical.untrop y)) := rfl

