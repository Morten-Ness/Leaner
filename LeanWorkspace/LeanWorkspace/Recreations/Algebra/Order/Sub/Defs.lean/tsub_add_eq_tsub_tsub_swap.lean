import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_add_eq_tsub_tsub_swap (a b c : α) : a - (b + c) = a - c - b := by
  rw [add_comm]
  apply tsub_add_eq_tsub_tsub

