import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 := (one_le a).lt_iff_ne.trans ne_comm

