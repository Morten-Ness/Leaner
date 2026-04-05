import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoid α]

theorem isRightRegular_ofAdd {a : α} :
    IsRightRegular (Multiplicative.ofAdd a) ↔ IsAddRightRegular a := .rfl

