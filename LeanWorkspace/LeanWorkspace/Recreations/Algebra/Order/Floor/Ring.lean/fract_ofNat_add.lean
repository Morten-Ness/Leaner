import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : R) :
    fract (ofNat(n) + a) = fract a := Int.fract_natCast_add n a

