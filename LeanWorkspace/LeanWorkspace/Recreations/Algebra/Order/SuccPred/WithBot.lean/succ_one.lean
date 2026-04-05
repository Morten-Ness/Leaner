import Mathlib

variable {α : Type*} [Preorder α] [OrderBot α] [AddMonoidWithOne α] [SuccAddOrder α]

theorem succ_one : succ (1 : WithBot α) = 2 := by
  simpa [one_add_one_eq_two] using WithBot.succ_natCast (α := α) 1

