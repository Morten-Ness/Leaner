import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) := rfl

