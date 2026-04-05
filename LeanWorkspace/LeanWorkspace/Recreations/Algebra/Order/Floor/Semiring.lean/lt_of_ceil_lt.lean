import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n := (Nat.le_ceil a).trans_lt (Nat.cast_lt.2 h)

