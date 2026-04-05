import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isLeftRegular_toLex {a : α} : IsLeftRegular (toLex a) ↔ IsLeftRegular a := .rfl

