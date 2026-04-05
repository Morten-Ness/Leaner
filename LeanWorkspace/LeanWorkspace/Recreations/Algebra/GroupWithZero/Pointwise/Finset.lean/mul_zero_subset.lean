import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [DecidableEq α] [MulZeroClass α] {s : Finset α}

theorem mul_zero_subset (s : Finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]

