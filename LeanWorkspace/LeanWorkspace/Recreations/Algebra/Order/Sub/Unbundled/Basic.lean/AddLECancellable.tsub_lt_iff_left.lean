import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_lt_iff_left (hb : AddLECancellable b) (hba : b ≤ a) :
    a - b < c ↔ a < b + c := by
  refine ⟨hb.lt_add_of_tsub_lt_left, ?_⟩
  intro h; refine (tsub_le_iff_left.mpr h.le).lt_of_ne ?_
  rintro rfl; exact h.ne' (add_tsub_cancel_of_le hba)

