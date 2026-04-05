import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRegular_toLex {a : α} : IsRegular (toLex a) ↔ IsRegular a := .rfl

