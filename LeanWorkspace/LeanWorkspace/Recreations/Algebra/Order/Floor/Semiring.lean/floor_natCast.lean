import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem floor_natCast (n : ℕ) : ⌊(n : R)⌋₊ = n := eq_of_forall_le_iff fun a => by
    rw [le_floor_iff, Nat.cast_le]
    exact n.cast_nonneg

