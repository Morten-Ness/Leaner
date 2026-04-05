import Mathlib

variable (R : Type u)

theorem untrop_zero [Top R] : Tropical.untrop (0 : Tropical R) = ⊤ := rfl

