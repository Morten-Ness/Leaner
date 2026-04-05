import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem self_sub_floor (a : R) : a - ⌊a⌋ = fract a := rfl

