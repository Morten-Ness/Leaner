import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommMonoid α] [Sub α] [OrderedSub α]

theorem tsub_zero (a : α) : a - 0 = a := AddLECancellable.tsub_eq_of_eq_add addLECancellable_zero (add_zero _).symm

