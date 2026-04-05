import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem isRightRegular_toMul {a : Additive α} : IsRightRegular a.toMul ↔ IsAddRightRegular a := .rfl

