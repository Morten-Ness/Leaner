import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_intCast (z : ℤ) : ⌊(z : R)⌋ = z := eq_of_forall_le_iff fun a => by rw [le_floor, Int.cast_le]

