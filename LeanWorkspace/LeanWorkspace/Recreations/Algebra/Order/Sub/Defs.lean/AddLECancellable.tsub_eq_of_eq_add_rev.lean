import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_eq_of_eq_add_rev (hb : AddLECancellable b) (h : a = b + c) : a - b = c := AddLECancellable.tsub_eq_of_eq_add hb <| by rw [add_comm, h]

