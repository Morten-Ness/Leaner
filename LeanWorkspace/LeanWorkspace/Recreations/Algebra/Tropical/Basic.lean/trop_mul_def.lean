import Mathlib

variable (R : Type u)

theorem trop_mul_def [Add R] (x y : Tropical R) : x * y = Tropical.trop (Tropical.untrop x + Tropical.untrop y) := rfl

