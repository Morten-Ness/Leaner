import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem eq_one_or_one_lt (a : α) : a = 1 ∨ 1 < a := (one_le a).eq_or_lt.imp_left Eq.symm

