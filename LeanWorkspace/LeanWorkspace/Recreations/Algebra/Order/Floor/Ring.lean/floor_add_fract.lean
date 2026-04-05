import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem floor_add_fract (a : R) : (⌊a⌋ : R) + fract a = a := add_sub_cancel _ _

