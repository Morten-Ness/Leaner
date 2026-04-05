import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_intCast (z : ℤ) : ⌈(z : R)⌉ = z := eq_of_forall_ge_iff fun a => by rw [ceil_le, Int.cast_le]

