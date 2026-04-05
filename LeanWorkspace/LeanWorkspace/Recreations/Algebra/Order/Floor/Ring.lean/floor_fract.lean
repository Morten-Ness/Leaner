import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem floor_fract (a : R) : ⌊fract a⌋ = 0 := by
  rw [Int.floor_eq_iff, Int.cast_zero, zero_add]; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

