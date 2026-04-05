import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := mod_cast Nat.lt_of_floor_lt h

