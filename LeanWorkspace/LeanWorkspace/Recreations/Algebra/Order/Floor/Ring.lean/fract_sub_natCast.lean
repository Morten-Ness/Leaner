import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_sub_natCast (a : R) (n : ℕ) : fract (a - n) = fract a := by
  rw [fract]
  simp

