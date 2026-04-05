import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_zero : fract (0 : R) = 0 := by rw [fract, Int.floor_zero, cast_zero, sub_self]

