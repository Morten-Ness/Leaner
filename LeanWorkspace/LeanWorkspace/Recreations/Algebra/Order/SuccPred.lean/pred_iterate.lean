import Mathlib

variable {α : Type*} {x y : α}

variable [Preorder α]

theorem pred_iterate [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : ℕ) :
    pred^[n] x = x - n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, sub_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, Order.pred_eq_sub_one, Nat.cast_one, sub_sub]

