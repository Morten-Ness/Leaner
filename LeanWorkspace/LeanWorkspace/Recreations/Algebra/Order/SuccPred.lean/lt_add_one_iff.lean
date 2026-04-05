import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x ≤ y := Order.lt_add_one_iff_of_not_isMax (not_isMax y)

