import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftMono α] [AddLeftReflectLE α]

theorem add_tsub_add_eq_tsub_right (a c b : α) : a + c - (b + c) = a - b := by
  refine add_tsub_add_le_tsub_right.antisymm (tsub_le_iff_right.2 <| ?_)
  apply le_of_add_le_add_right
  rw [add_assoc]
  exact le_tsub_add

