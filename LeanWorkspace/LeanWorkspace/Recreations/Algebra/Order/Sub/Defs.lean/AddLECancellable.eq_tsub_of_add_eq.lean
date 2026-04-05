import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem eq_tsub_of_add_eq (hc : AddLECancellable c) (h : a + c = b) : a = b - c := (AddLECancellable.tsub_eq_of_eq_add hc h.symm).symm

