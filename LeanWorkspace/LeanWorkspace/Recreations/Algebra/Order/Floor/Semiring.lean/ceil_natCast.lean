import Mathlib

variable {R K : Type*}

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

variable [IsStrictOrderedRing R]

theorem ceil_natCast (n : ℕ) : ⌈(n : R)⌉₊ = n := eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]

