import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem Icc_sub_one_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico_of_not_isMin hb a

