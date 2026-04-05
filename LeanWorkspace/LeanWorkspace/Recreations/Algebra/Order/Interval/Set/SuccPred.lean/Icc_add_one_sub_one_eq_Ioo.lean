import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [Add α] [Sub α] [SuccAddOrder α] [PredSubOrder α] [Nontrivial α]

theorem Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b := by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

