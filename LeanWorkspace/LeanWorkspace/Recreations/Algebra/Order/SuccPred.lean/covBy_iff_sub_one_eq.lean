import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem covBy_iff_sub_one_eq [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] :
    x ⋖ y ↔ y - 1 = x := by
  rw [← Order.pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm

