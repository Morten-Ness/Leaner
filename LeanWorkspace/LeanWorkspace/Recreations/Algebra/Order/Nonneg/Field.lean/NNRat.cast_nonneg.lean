import Mathlib

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem NNRat.cast_nonneg (q : ℚ≥0) : 0 ≤ (q : α) := by
  rw [cast_def]; exact div_nonneg q.num.cast_nonneg q.den.cast_nonneg

