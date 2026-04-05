import Mathlib

variable {α : Type*}

variable [Preorder α]

theorem ofAdd_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b := Iff.rfl

