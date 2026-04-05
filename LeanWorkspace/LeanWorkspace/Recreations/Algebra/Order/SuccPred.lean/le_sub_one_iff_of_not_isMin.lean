import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem le_sub_one_iff_of_not_isMin (hy : ¬ IsMin y) : x ≤ y - 1 ↔ x < y := by
  rw [← Order.pred_eq_sub_one, le_pred_iff_of_not_isMin hy]

