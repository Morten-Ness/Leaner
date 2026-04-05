import Mathlib

variable {α : Type*}

theorem val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b := Iff.rfl

