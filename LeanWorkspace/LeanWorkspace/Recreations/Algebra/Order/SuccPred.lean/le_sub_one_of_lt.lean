import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem le_sub_one_of_lt (h : x < y) : x ≤ y - 1 := by
  rw [← Order.pred_eq_sub_one]
  exact le_pred_of_lt h

