import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem add_tsub_tsub_cancel (h : c ≤ a) : a + b - (a - c) = b + c := Contravariant.AddLECancellable.add_tsub_tsub_cancel h

