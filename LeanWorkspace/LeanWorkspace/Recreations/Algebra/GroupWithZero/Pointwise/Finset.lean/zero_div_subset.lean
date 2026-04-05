import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

theorem zero_div_subset (s : Finset α) : 0 / s ⊆ 0 := by simp [subset_iff, mem_div]

