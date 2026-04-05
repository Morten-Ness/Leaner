import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem add_tsub_cancel_right (a b : α) : a + b - b = a := Contravariant.AddLECancellable.add_tsub_cancel_right

