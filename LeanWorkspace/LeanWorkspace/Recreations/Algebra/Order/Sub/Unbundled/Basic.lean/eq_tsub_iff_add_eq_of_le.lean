import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem eq_tsub_iff_add_eq_of_le (h : c ≤ b) : a = b - c ↔ a + c = b := Contravariant.AddLECancellable.eq_tsub_iff_add_eq_of_le h

