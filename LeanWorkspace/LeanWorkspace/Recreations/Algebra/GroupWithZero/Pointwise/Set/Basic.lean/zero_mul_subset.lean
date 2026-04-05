import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [MulZeroClass α] {s : Set α}

theorem zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]

