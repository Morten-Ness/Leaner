import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 := (one_le a).ge_iff_eq'

