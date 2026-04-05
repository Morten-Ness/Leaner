import Mathlib

variable (R : Type u)

theorem trop_top [Top R] : Tropical.trop (⊤ : R) = 0 := rfl

