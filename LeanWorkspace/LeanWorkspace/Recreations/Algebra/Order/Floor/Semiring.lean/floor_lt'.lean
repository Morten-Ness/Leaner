import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_lt' (hn : n ≠ 0) : ⌊a⌋₊ < n ↔ a < n := lt_iff_lt_of_le_iff_le <| Nat.le_floor_iff' hn

