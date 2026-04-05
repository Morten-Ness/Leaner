import Mathlib

variable (R : Type u)

theorem rightInverse_trop : Function.RightInverse (Tropical.trop : R → Tropical R) Tropical.untrop := Tropical.untrop_trop

