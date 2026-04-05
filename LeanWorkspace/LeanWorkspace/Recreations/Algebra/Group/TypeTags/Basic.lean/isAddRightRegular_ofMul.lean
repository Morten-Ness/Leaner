import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem isAddRightRegular_ofMul {a : α} : IsAddRightRegular (Additive.ofMul a) ↔ IsRightRegular a := .rfl

