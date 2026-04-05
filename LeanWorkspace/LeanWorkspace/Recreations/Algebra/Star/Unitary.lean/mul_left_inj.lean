import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem mul_left_inj {x y : R} (U : unitary R) :
    x * U = y * U ↔ x = y := val_toUnits_apply U ▸ Units.mul_left_inj _

