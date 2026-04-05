import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem insert_Ioc_sub_one_right_eq_Ioc (h : a < b) : insert b (Ioc a (b - 1)) = Ioc a b := by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h

