import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_tsub_tsub_cancel_left (hab : AddLECancellable (a - b)) (h : b ≤ a) :
    a - c - (a - b) = b - c := by rw [tsub_right_comm, AddLECancellable.tsub_tsub_cancel_of_le hab h]

