import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

variable [NoMinOrder α]

theorem Ioo_sub_one_left_eq_Ioc (a b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b

