import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_one_add (a : R) : fract (1 + a) = fract a := mod_cast Int.fract_natCast_add 1 a

