import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrder α]

variable [Sub α] [PredSubOrder α] {a b : α}

variable [NoMinOrder α]

theorem insert_Ioc_left_eq_Ioc_sub_one (h : a ≤ b) : insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred h

