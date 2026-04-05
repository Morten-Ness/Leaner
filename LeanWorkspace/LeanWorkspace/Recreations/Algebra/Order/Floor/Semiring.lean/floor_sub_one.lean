import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_sub_one [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) : ⌊a - 1⌋₊ = ⌊a⌋₊ - 1 := mod_cast Nat.floor_sub_natCast a 1

