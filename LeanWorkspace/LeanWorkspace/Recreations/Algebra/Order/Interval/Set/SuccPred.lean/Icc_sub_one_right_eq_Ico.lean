import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

variable [NoMinOrder α]

theorem Icc_sub_one_right_eq_Ico (a b : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b

