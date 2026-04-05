import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_natCast_add (n : ℕ) (a : R) : fract (↑n + a) = fract a := by
  rw [add_comm, Int.fract_add_natCast]

