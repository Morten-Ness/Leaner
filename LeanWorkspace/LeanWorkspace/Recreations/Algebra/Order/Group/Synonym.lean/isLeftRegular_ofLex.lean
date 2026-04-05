import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isLeftRegular_ofLex {a : Lex α} : IsLeftRegular (ofLex a) ↔ IsLeftRegular a := .rfl

