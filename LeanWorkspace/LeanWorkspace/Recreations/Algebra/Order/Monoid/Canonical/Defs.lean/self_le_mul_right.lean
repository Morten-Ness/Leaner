import Mathlib

variable {α : Type u}

variable [Mul α]

variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

theorem self_le_mul_right (a b : α) : a ≤ a * b := le_self_mul

