import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem mul_right_inj {x y : R} (U : unitary R) :
    U * x = U * y ↔ x = y := val_toUnits_apply U ▸ Units.mul_right_inj _

