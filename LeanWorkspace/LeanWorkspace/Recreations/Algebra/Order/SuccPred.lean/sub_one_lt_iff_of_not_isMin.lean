import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem sub_one_lt_iff_of_not_isMin (hx : ¬ IsMin x) : x - 1 < y ↔ x ≤ y := by
  rw [← Order.pred_eq_sub_one, pred_lt_iff_of_not_isMin hx]

