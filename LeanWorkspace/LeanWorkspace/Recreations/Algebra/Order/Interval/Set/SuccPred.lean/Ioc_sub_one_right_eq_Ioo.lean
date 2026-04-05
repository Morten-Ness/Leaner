import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem Ioc_sub_one_right_eq_Ioo (a b : α) : Ioc a (b - 1) = Ioo a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_right_eq_Ioo a b

