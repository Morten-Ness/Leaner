import Mathlib

variable {α : Type*}

variable [Preorder α]

theorem toAdd_le {a b : Multiplicative α} : a.toAdd ≤ b.toAdd ↔ a ≤ b := Iff.rfl

