import Mathlib

variable {α : Type*} {x y : α}

variable [LinearOrder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem le_of_lt_add_one (h : x < y + 1) : x ≤ y := by
  rw [← Order.succ_eq_add_one] at h
  exact le_of_lt_succ h

