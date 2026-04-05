import Mathlib

variable (R : Type u)

theorem untrop_div [Sub R] (x y : Tropical R) : Tropical.untrop (x / y) = Tropical.untrop x - Tropical.untrop y := rfl

