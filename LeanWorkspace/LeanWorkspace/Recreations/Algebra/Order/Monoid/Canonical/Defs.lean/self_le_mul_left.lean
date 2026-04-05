import Mathlib

variable {α : Type u}

variable [Mul α]

variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

theorem self_le_mul_left (a b : α) : a ≤ b * a := le_mul_self

