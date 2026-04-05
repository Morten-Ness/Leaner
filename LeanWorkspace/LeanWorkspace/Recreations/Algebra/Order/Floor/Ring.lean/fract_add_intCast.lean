import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_add_intCast (a : R) (m : ℤ) : fract (a + m) = fract a := by
  rw [fract]
  simp

