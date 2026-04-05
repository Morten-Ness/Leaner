import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_natCast (n : ℕ) : ⌊(n : R)⌋ = n := eq_of_forall_le_iff fun a => by rw [le_floor, ← cast_natCast, cast_le]

