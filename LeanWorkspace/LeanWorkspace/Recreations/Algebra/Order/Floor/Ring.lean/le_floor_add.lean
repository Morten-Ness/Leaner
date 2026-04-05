import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem le_floor_add (a b : R) : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := by
  rw [le_floor, Int.cast_add]
  gcongr <;> apply floor_le

