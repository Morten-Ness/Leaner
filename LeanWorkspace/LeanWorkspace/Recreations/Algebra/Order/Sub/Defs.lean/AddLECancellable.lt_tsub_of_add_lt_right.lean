import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem lt_tsub_of_add_lt_right (hc : AddLECancellable c) (h : a + c < b) : a < b - c := (AddLECancellable.le_tsub_of_add_le_right hc h.le).lt_of_ne <| by
    rintro rfl
    exact h.not_ge le_tsub_add

