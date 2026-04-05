import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem covBy_add_one [NoMaxOrder α] (x : α) : x ⋖ x + 1 := by
  rw [← Order.succ_eq_add_one]
  exact covBy_succ x

