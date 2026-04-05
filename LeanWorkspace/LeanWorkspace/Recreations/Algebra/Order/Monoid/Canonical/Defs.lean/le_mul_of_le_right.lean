import Mathlib

variable {α : Type u}

variable [Mul α]

variable [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_mul_of_le_right : a ≤ c → a ≤ b * c := le_mul_self.trans'

