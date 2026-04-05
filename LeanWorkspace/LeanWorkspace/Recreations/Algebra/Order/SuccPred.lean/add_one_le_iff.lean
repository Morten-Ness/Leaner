import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem add_one_le_iff [NoMaxOrder α] : x + 1 ≤ y ↔ x < y := Order.add_one_le_iff_of_not_isMax (not_isMax x)

