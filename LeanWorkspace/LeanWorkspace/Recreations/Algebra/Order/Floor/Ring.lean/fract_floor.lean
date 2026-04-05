import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_floor (a : R) : fract (⌊a⌋ : R) = 0 := Int.fract_intCast _

