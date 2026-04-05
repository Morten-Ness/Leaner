import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_ofNat (n : ℕ) [n.AtLeastTwo] :
    fract (ofNat(n) : R) = 0 := Int.fract_natCast n

