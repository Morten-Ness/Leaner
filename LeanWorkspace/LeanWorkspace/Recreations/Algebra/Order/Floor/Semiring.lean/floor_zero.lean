import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_zero : ⌊(0 : R)⌋₊ = 0 := by rw [← Nat.cast_zero, Nat.floor_natCast]

