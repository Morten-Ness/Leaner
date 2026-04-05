import Mathlib

variable {α β : Type*}

variable [Monoid α]

theorem isRightRegular_ofLex {a : Lex α} : IsRightRegular (ofLex a) ↔ IsRightRegular a := .rfl

