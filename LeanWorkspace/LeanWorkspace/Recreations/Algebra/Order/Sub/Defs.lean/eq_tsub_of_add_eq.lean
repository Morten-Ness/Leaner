import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem eq_tsub_of_add_eq (h : a + c = b) : a = b - c := Contravariant.AddLECancellable.eq_tsub_of_add_eq h

