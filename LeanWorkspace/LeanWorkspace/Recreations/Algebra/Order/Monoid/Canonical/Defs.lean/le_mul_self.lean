import Mathlib

variable {α : Type u}

variable [Mul α]

variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_mul_self : a ≤ b * a := CanonicallyOrderedMul.le_mul_self _ _

