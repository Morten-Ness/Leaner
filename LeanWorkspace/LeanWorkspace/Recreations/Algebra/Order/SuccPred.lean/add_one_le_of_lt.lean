import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem add_one_le_of_lt (h : x < y) : x + 1 ≤ y := by
  rw [← Order.succ_eq_add_one]
  exact succ_le_of_lt h

