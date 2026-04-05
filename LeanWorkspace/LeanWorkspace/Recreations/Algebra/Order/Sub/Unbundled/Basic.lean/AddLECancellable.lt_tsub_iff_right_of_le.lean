import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem lt_tsub_iff_right_of_le (hc : AddLECancellable c) (h : c ≤ b) :
    a < b - c ↔ a + c < b := by
  refine ⟨fun h' => (add_le_of_le_tsub_right_of_le h h'.le).lt_of_ne ?_, hc.lt_tsub_of_add_lt_right⟩
  rintro rfl
  exact h'.ne' hc.add_tsub_cancel_right

