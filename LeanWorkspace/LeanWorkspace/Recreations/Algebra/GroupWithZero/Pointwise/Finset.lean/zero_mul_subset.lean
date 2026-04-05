import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

theorem zero_mul_subset (s : Finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]

