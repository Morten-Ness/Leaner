import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

variable [AddLeftReflectLE α]

theorem lt_tsub_of_add_lt_right : a + c < b → a < b - c := Contravariant.AddLECancellable.lt_tsub_of_add_lt_right

