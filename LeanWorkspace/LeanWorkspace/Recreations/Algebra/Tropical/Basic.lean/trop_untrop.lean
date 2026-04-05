import Mathlib

variable (R : Type u)

theorem trop_untrop (x : Tropical R) : Tropical.trop (Tropical.untrop x) = x := rfl

