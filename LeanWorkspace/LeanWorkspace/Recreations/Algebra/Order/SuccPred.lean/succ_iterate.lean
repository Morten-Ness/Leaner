import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

theorem succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : ℕ) :
    succ^[n] x = x + n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, Order.succ_eq_add_one, Nat.cast_one, add_assoc]

