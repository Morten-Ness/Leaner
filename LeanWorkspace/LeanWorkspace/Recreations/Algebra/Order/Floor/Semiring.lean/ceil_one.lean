import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem ceil_one : ⌈(1 : R)⌉₊ = 1 := by rw [← Nat.cast_one, Nat.ceil_natCast]

