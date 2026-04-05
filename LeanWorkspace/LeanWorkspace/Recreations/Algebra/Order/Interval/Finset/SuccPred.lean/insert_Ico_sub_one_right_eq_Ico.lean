import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem insert_Ico_sub_one_right_eq_Ico (h : a < b) : insert (b - 1) (Ico a (b - 1)) = Ico a b := by
  simpa [pred_eq_sub_one] using insert_Ico_pred_right_eq_Ico h

