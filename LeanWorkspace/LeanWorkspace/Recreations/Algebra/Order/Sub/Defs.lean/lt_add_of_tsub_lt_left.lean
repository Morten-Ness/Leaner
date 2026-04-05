import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem lt_add_of_tsub_lt_left (h : a - b < c) : a < b + c := Contravariant.AddLECancellable.lt_add_of_tsub_lt_left h

