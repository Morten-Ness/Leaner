import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem le_sub_one_iff [NoMinOrder α] : x ≤ y - 1 ↔ x < y := Order.le_sub_one_iff_of_not_isMin (not_isMin y)

