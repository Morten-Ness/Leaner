import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α]

theorem zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 2 := by
  rw [← one_add_one_eq_two]
  exact add_nonneg zero_le_one zero_le_one

