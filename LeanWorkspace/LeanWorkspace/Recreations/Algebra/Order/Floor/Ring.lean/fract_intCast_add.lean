import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_intCast_add (m : ℤ) (a : R) : fract (↑m + a) = fract a := by
  rw [add_comm, Int.fract_add_intCast]

