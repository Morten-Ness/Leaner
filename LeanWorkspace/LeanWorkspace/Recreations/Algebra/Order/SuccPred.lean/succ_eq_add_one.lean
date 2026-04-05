import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

variable [Add α] [One α] [SuccAddOrder α]

theorem succ_eq_add_one (x : α) : succ x = x + 1 := SuccAddOrder.succ_eq_add_one x

