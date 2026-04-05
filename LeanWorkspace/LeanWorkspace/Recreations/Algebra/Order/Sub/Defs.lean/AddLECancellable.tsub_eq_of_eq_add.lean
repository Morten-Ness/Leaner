import Mathlib

variable {α : Type*}

variable [PartialOrder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] {a b c d : α}

theorem tsub_eq_of_eq_add (hb : AddLECancellable b) (h : a = c + b) : a - b = c := le_antisymm (tsub_le_iff_right.mpr h.le) <| by
    rw [h]
    exact AddLECancellable.le_add_tsub hb

