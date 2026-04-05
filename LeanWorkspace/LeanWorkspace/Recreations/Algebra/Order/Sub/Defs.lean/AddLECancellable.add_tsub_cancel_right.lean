import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem add_tsub_cancel_right (hb : AddLECancellable b) : a + b - b = a := AddLECancellable.tsub_eq_of_eq_add hb <| by rw [add_comm]

