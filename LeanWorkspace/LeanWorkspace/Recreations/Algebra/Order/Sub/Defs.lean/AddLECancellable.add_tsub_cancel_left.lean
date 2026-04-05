import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem add_tsub_cancel_left (ha : AddLECancellable a) : a + b - a = b := AddLECancellable.tsub_eq_of_eq_add ha <| add_comm a b

