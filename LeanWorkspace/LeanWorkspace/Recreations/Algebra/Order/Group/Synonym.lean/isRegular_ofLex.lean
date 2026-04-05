import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRegular_ofLex {a : Lex α} : IsRegular (ofLex a) ↔ IsRegular a := .rfl

