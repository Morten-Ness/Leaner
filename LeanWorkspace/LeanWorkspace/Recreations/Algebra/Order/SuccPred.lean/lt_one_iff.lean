import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [AddMonoidWithOne α] [NoMaxOrder α] [SuccAddOrder α]

theorem lt_one_iff [CanonicallyOrderedAdd α] : x < 1 ↔ x = 0 := by
  rw [← zero_add 1, Order.lt_add_one_iff, nonpos_iff_eq_zero]

