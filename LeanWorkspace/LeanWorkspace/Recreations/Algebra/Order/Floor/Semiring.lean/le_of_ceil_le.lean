import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem le_of_ceil_le (h : ⌈a⌉₊ ≤ n) : a ≤ n := (Nat.le_ceil a).trans (Nat.cast_le.2 h)

