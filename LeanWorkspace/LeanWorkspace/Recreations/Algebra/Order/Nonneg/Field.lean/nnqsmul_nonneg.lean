import Mathlib

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem nnqsmul_nonneg (q : ℚ≥0) (ha : 0 ≤ a) : 0 ≤ q • a := by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

