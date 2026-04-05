import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoid α]

theorem isAddLeftRegular_toAdd {a : Multiplicative α} : IsAddLeftRegular a.toAdd ↔ IsLeftRegular a := .rfl

