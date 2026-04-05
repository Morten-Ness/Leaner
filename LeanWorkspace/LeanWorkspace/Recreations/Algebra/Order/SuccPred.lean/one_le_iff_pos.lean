import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : 1 ≤ x ↔ 0 < x := by
  rw [← succ_le_iff_of_not_isMax Order.not_isMax_zero, Order.succ_eq_add_one, zero_add]

