import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_add_one (a : R) : ⌈a + 1⌉ = ⌈a⌉ + 1 := by
  rw [← Int.ceil_add_intCast a (1 : ℤ), cast_one]

