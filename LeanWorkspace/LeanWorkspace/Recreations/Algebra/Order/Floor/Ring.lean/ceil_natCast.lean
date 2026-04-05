import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_natCast (n : ℕ) : ⌈(n : R)⌉ = n := eq_of_forall_ge_iff fun a => by rw [ceil_le, ← cast_natCast, cast_le]

