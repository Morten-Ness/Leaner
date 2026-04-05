import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem self_sub_fract (a : R) : a - fract a = ⌊a⌋ := sub_sub_cancel _ _

