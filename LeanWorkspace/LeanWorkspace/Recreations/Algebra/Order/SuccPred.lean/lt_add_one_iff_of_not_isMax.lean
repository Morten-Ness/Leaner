import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem lt_add_one_iff_of_not_isMax (hy : ¬ IsMax y) : x < y + 1 ↔ x ≤ y := by
  rw [← Order.succ_eq_add_one, lt_succ_iff_of_not_isMax hy]

