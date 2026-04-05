import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isLeftRegular_toDual {a : α} : IsLeftRegular (toDual a) ↔ IsLeftRegular a := .rfl

