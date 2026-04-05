import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_eq_tsub_of_add_eq_add (h : a + d = c + b) : a - b = c - d := by
  calc a - b = a + d - d - b := by rw [add_tsub_cancel_right]
           _ = c + b - b - d := by rw [h, tsub_right_comm]
           _ = c - d := by rw [add_tsub_cancel_right]

