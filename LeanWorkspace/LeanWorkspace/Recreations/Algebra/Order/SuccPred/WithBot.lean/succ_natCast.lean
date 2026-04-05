import Mathlib

variable {α : Type*} [Preorder α] [OrderBot α] [AddMonoidWithOne α] [SuccAddOrder α]

theorem succ_natCast (n : ℕ) : succ (n : WithBot α) = n + 1 := by
  rw [← WithBot.coe_natCast, succ_coe, Order.succ_eq_add_one]

