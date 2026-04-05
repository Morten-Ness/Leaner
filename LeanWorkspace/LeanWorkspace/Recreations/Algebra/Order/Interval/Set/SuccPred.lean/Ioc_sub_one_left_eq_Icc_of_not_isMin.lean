import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem Ioc_sub_one_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc_of_not_isMin ha b

