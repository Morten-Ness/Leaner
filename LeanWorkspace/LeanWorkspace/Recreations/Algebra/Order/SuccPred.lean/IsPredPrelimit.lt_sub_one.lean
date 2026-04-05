import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem IsPredPrelimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : x < y - 1 := by
  rw [← Order.pred_eq_sub_one]
  exact hx.lt_pred hy

