import Mathlib

variable (R : Type u)

theorem untrop_inv [Neg R] (x : Tropical R) : Tropical.untrop x⁻¹ = -Tropical.untrop x := rfl

