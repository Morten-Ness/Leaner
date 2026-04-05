import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

theorem lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : x < 1 ↔ x ≤ 0 := by
  rw [← lt_succ_iff_of_not_isMax Order.not_isMax_zero, Order.succ_eq_add_one, zero_add]

