import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem tsub_eq_of_eq_add (h : a = c + b) : a - b = c := Contravariant.AddLECancellable.tsub_eq_of_eq_add h

