import Mathlib

variable {α : Type u}

variable [Mul α]

variable [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_mul_of_le_left : a ≤ b → a ≤ b * c := le_self_mul.trans'

