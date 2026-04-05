import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRightRegular_toColex {a : α} : IsRightRegular (toColex a) ↔ IsRightRegular a := .rfl

