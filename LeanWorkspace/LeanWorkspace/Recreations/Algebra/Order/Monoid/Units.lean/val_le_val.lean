import Mathlib

variable {α : Type*}

theorem val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b := Iff.rfl

