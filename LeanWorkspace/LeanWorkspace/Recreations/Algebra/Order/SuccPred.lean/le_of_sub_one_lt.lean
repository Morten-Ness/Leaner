import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [Sub α] [One α] [PredSubOrder α]

theorem le_of_sub_one_lt (h : x - 1 < y) : x ≤ y := by
  rw [← Order.pred_eq_sub_one] at h
  exact le_of_pred_lt h

