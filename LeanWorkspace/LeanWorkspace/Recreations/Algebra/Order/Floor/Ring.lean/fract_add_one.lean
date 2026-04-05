import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_add_one (a : R) : fract (a + 1) = fract a := mod_cast Int.fract_add_natCast a 1

