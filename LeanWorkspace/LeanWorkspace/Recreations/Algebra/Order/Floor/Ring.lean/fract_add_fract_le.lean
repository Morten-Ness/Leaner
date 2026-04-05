import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem fract_add_fract_le (a b : R) : fract a + fract b ≤ fract (a + b) + 1 := by
  rw [fract, fract, fract, sub_add_sub_comm, sub_add, sub_le_sub_iff_left]
  exact mod_cast Int.le_floor_add_floor a b

