import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem add_one_le_iff_of_not_isMax (hx : ¬ IsMax x) : x + 1 ≤ y ↔ x < y := by
  rw [← Order.succ_eq_add_one, succ_le_iff_of_not_isMax hx]

