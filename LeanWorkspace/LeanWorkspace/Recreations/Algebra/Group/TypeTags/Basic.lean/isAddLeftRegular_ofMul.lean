import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem isAddLeftRegular_ofMul {a : α} : IsAddLeftRegular (Additive.ofMul a) ↔ IsLeftRegular a := .rfl

