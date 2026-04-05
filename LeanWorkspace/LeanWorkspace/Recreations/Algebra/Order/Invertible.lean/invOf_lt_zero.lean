import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R}

theorem invOf_lt_zero [Invertible a] : ⅟a < 0 ↔ a < 0 := by simp only [← not_le, invOf_nonneg]

