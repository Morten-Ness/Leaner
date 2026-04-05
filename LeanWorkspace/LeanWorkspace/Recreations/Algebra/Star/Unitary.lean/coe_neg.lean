import Mathlib

variable {R : Type*}

variable [Ring R] [StarRing R]

theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) := rfl

