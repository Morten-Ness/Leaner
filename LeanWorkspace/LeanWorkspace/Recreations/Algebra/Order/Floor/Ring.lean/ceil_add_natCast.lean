import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_add_natCast (a : R) (n : ℕ) : ⌈a + n⌉ = ⌈a⌉ + n := by
  rw [← Int.cast_natCast, Int.ceil_add_intCast]

