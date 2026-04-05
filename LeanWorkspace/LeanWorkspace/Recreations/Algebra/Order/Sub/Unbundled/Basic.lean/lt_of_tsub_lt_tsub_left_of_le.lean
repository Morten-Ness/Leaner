import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem lt_of_tsub_lt_tsub_left_of_le [AddLeftReflectLT α] (hca : c ≤ a)
    (h : a - b < a - c) : c < b := Contravariant.AddLECancellable.lt_of_tsub_lt_tsub_left_of_le hca h

