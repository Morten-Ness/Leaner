import Mathlib

variable {α : Type*}

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b c : α}

variable [AddLeftReflectLE α]

theorem tsub_lt_self : 0 < a → 0 < b → a - b < a := Contravariant.AddLECancellable.tsub_lt_self

