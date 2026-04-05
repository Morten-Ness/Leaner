import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoid α]

theorem isLeftRegular_ofAdd {a : α} : IsLeftRegular (Multiplicative.ofAdd a) ↔ IsAddLeftRegular a := .rfl

