import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [LE α] [CanonicallyOrderedMul α] {a b : α}

theorem one_le (a : α) : 1 ≤ a := le_self_mul.trans_eq (one_mul _)

