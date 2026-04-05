import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem one_lt_of_ne_one (h : a ≠ 1) : 1 < a := one_lt_iff_ne_one.2 h

