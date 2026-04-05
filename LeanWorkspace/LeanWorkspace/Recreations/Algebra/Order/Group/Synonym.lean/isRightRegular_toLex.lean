import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRightRegular_toLex {a : α} : IsRightRegular (toLex a) ↔ IsRightRegular a := .rfl

