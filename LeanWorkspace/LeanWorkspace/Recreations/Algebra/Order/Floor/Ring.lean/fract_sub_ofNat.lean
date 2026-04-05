import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_sub_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    fract (a - ofNat(n)) = fract a := Int.fract_sub_natCast a n

-- Was a duplicate lemma under a bad name

