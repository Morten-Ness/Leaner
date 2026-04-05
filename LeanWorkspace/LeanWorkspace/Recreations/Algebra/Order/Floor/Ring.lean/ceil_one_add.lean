import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_one_add (a : R) : ⌈1 + a⌉ = 1 + ⌈a⌉ := mod_cast Int.ceil_natCast_add 1 a

