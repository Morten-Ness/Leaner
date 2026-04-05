import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_tsub_cancel_of_le (h : a ≤ b) : b - (b - a) = a := Contravariant.AddLECancellable.tsub_tsub_cancel_of_le h

