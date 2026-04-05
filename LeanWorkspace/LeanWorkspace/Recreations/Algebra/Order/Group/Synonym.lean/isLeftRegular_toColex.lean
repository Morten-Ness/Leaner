import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isLeftRegular_toColex {a : α} : IsLeftRegular (toColex a) ↔ IsLeftRegular a := .rfl

