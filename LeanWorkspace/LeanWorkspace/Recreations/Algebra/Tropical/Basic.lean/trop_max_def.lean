import Mathlib

variable (R : Type u)

variable [LinearOrder R]

theorem trop_max_def (x y : Tropical R) : max x y = Tropical.trop (max (Tropical.untrop x) (Tropical.untrop y)) := rfl

