import Mathlib

variable (R : Type u)

theorem trop_zero [Zero R] : Tropical.trop (0 : R) = 1 := rfl

