import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_tsub_eq_add_tsub_of_le
    (h : c ≤ b) : a - (b - c) = a + c - b := by
  obtain ⟨d, rfl⟩ := exists_add_of_le h
  rw [add_tsub_cancel_left c, add_comm a c, add_tsub_add_eq_tsub_left]

