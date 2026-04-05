import Mathlib

variable {α : Type*}

variable [AddMonoidWithOne α]

theorem zero_le_three [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 3 := by
  rw [← two_add_one_eq_three]
  exact add_nonneg zero_le_two zero_le_one

