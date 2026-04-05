import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem lt_tsub_of_add_lt_left (ha : AddLECancellable a) (h : a + c < b) : c < b - a := AddLECancellable.lt_tsub_of_add_lt_right ha <| by rwa [add_comm]

