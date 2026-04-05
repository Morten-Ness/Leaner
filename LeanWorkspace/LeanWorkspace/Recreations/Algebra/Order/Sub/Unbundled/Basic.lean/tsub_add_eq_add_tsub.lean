import Mathlib

variable {α : Type*}

variable [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [AddLeftMono α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_add_eq_add_tsub (h : b ≤ a) : a - b + c = a + c - b := Contravariant.AddLECancellable.tsub_add_eq_add_tsub h

