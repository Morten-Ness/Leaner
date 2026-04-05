import Mathlib

variable {α : Type*}

variable [Preorder α]

theorem toMul_le {a b : Additive α} : a.toMul ≤ b.toMul ↔ a ≤ b := Iff.rfl

