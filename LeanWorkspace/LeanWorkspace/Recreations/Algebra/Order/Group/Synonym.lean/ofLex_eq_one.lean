import Mathlib

variable {α β : Type*}

theorem ofLex_eq_one [One α] {a : Lex α} : ofLex a = 1 ↔ a = 1 := .rfl

