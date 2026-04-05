import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [MulZeroClass α] {s : Set α}

theorem mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]

