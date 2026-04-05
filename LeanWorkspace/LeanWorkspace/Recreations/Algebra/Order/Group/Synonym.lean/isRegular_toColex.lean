import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRegular_toColex {a : α} : IsRegular (toColex a) ↔ IsRegular a := .rfl

