import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem sub_one_lt_iff [NoMinOrder α] : x - 1 < y ↔ x ≤ y := Order.sub_one_lt_iff_of_not_isMin (not_isMin x)

