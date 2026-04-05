import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_zero : ⌊(0 : R)⌋ = 0 := by rw [← cast_zero, Int.floor_intCast]

