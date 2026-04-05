import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Sub α] [PredSubOrder α] {a b : α}

theorem insert_Icc_left_eq_Icc_sub_one (h : a - 1 ≤ b) :
    insert (a - 1) (Icc a b) = Icc (a - 1) b := by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)

