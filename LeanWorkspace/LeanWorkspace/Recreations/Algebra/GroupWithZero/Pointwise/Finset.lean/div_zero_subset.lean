import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [GroupWithZero α] [DecidableEq α] {s : Finset α}

theorem div_zero_subset (s : Finset α) : s / 0 ⊆ 0 := by simp [subset_iff, mem_div]

