import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem isLeftRegular_toMul {a : Additive α} : IsLeftRegular a.toMul ↔ IsAddLeftRegular a := .rfl

