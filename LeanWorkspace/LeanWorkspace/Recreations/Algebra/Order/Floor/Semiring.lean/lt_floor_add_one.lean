import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1 := by simpa using Nat.lt_succ_floor a

