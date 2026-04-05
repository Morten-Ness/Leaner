import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : R) :
    ⌊ofNat(n) + a⌋ = ofNat(n) + ⌊a⌋ := Int.floor_natCast_add n a

