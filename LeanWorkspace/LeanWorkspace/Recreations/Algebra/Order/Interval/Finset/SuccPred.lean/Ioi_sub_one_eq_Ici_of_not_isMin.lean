import Mathlib

variable {ι α : Type*}

variable [LinearOrder α] [One α]

variable [LocallyFiniteOrderTop α]

variable [Sub α] [PredSubOrder α] {a a : α}

theorem Ioi_sub_one_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici_of_not_isMin ha

