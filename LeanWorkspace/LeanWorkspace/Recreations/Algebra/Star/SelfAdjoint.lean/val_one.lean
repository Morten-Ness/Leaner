import Mathlib

variable {R A : Type*}

variable [Ring R] [StarRing R]

theorem val_one : ↑(1 : selfAdjoint R) = (1 : R) := rfl

