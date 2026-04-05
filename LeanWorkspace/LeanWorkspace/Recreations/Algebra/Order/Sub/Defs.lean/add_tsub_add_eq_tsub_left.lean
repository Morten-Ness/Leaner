import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α] [AddLeftReflectLE α]

theorem add_tsub_add_eq_tsub_left (a b c : α) : a + b - (a + c) = b - c := by
  rw [add_comm a b, add_comm a c, add_tsub_add_eq_tsub_right]

