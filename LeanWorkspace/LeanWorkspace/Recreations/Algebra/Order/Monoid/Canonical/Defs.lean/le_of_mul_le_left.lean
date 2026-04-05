import Mathlib

variable {α : Type u}

variable [Mul α]

variable [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_of_mul_le_left : a * b ≤ c → a ≤ c := le_self_mul.trans

