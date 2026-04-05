import Mathlib

variable (R : Type u)

theorem untrop_one [Zero R] : Tropical.untrop (1 : Tropical R) = 0 := rfl

