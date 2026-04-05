import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [AddMonoidWithOne α] [NoMaxOrder α] [SuccAddOrder α]

theorem lt_two_iff : x < 2 ↔ x ≤ 1 := by
  rw [← one_add_one_eq_two, Order.lt_add_one_iff]

