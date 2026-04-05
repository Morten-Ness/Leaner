import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_intCast (z : ℤ) : fract (z : R) = 0 := by
  unfold fract
  rw [Int.floor_intCast]
  exact sub_self _

