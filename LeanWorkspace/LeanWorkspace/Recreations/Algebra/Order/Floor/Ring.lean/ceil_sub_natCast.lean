import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_sub_natCast (a : R) (n : ℕ) : ⌈a - n⌉ = ⌈a⌉ - n := by
  convert Int.ceil_sub_intCast a n using 1
  simp

