import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem fract_sub_self (a : R) : fract a - a = -⌊a⌋ := sub_sub_cancel_left _ _

