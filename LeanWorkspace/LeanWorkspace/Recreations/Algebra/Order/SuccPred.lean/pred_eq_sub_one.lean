import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem pred_eq_sub_one (x : α) : pred x = x - 1 := PredSubOrder.pred_eq_sub_one x

