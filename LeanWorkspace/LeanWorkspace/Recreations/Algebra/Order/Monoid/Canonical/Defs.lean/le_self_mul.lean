import Mathlib

variable {α : Type u}

variable [Mul α]

variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_self_mul : a ≤ a * b := CanonicallyOrderedMul.le_self_mul _ _

