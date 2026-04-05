import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem sub_one_covBy [NoMinOrder α] (x : α) : x - 1 ⋖ x := by
  rw [← Order.pred_eq_sub_one]
  exact pred_covBy x

