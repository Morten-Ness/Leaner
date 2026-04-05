import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_add_eq_add_tsub (hb : AddLECancellable b) (h : b ≤ a) :
    a - b + c = a + c - b := by rw [add_comm a, AddLECancellable.add_tsub_assoc_of_le hb h, add_comm]

