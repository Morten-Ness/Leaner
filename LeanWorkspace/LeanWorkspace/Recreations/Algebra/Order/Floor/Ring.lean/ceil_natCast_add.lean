import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_natCast_add (n : ℕ) (a : R) : ⌈n + a⌉ = n + ⌈a⌉ := mod_cast Int.ceil_intCast_add n a

