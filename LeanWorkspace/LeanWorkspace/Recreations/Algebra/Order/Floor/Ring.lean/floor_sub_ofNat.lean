import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_sub_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋ = ⌊a⌋ - ofNat(n) := Int.floor_sub_natCast a n

