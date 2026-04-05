import Mathlib

variable {α : Type*}

variable [Preorder α]

theorem ofMul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b := Iff.rfl

