import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n := lt_of_not_ge fun h' => (le_floor h').not_gt h

