import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_lt_tsub_iff_left_of_le_of_le [AddLeftReflectLT α] (h₁ : b ≤ a)
    (h₂ : c ≤ a) : a - b < a - c ↔ c < b := Contravariant.AddLECancellable.tsub_lt_tsub_iff_left_of_le_of_le Contravariant.AddLECancellable h₁
    h₂

