import Mathlib

variable {α : Type u}

variable [Mul α]

variable [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

theorem le_of_mul_le_right : a * b ≤ c → b ≤ c := le_mul_self.trans

