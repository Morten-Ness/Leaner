import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem insert_Icc_sub_one_right_eq_Icc (h : a ≤ b) : insert b (Icc a (b - 1)) = Icc a b := by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h

