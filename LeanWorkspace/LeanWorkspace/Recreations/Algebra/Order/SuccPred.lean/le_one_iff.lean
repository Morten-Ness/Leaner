import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [AddMonoidWithOne α] [NoMaxOrder α] [SuccAddOrder α]

theorem le_one_iff [CanonicallyOrderedAdd α] : x ≤ 1 ↔ x = 0 ∨ x = 1 := by
  rw [le_iff_lt_or_eq, Order.lt_one_iff]

