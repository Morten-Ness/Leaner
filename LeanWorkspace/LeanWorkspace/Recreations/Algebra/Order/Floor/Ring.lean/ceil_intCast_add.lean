import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_intCast_add (z : ℤ) (a : R) : ⌈z + a⌉ = z + ⌈a⌉ := by
  rw [add_comm, Int.ceil_add_intCast, add_comm]

