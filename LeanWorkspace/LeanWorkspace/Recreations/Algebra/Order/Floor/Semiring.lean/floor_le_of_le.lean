import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_le_of_le (h : a ≤ n) : ⌊a⌋₊ ≤ n := le_imp_le_iff_lt_imp_lt.2 Nat.lt_of_lt_floor h

