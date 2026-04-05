import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem fract_add_floor (a : R) : fract a + ⌊a⌋ = a := sub_add_cancel _ _

