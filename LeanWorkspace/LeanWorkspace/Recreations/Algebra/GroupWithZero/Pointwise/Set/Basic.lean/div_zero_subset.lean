import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] {s : Set α}

theorem div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]

