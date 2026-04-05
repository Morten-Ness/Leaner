import Mathlib

variable {α : Type u}

variable [Add α]

variable [Preorder α] (a b : WithZero (Multiplicative α))

theorem toMulBot_le : WithZero.toMulBot a ≤ WithZero.toMulBot b ↔ a ≤ b := Iff.rfl

