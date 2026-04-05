import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem insert_Ico_left_eq_Ico_sub_one_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (a - 1) (Ico a b) = Ico (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ico_left_eq_Ico_pred_of_not_isMin h ha

