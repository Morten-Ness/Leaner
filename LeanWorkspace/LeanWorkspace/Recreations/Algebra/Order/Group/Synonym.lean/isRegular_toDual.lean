import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRegular_toDual {a : α} : IsRegular (toDual a) ↔ IsRegular a := .rfl

