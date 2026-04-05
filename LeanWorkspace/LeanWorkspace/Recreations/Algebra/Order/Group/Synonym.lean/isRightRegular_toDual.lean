import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRightRegular_toDual {a : α} : IsRightRegular (toDual a) ↔ IsRightRegular a := .rfl

