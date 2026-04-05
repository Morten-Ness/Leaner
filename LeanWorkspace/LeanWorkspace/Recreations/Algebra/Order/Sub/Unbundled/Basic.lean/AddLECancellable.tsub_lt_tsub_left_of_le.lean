import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_lt_tsub_left_of_le (hab : AddLECancellable (a - b)) (h₁ : b ≤ a)
    (h : c < b) : a - b < a - c := (tsub_le_tsub_left h.le _).lt_of_ne fun h' => h.ne' <| AddLECancellable.tsub_inj_right hab h₁ (h.le.trans h₁) h'

