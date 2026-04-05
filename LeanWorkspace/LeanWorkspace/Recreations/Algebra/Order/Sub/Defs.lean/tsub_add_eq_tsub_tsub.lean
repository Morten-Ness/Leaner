import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) = a - b - c := (tsub_tsub _ _ _).symm

