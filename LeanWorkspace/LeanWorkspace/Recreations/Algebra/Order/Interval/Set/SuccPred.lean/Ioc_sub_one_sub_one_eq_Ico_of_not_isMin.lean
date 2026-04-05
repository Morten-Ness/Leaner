import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem Ioc_sub_one_sub_one_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico_of_not_isMin ha b

