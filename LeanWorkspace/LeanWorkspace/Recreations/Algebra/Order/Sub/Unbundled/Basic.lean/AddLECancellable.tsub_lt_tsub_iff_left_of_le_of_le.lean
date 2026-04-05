import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α]
    (hb : AddLECancellable b) (hab : AddLECancellable (a - b)) (h₁ : b ≤ a) (h₂ : c ≤ a) :
    a - b < a - c ↔ c < b := ⟨AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hb h₂, AddLECancellable.tsub_lt_tsub_left_of_le hab h₁⟩

