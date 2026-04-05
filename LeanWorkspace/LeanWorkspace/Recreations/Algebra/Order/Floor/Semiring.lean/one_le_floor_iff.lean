import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem one_le_floor_iff (x : R) : 1 ≤ ⌊x⌋₊ ↔ 1 ≤ x := mod_cast Nat.le_floor_iff' one_ne_zero

