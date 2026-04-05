import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_add_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    fract (a + ofNat(n)) = fract a := Int.fract_add_natCast a n

