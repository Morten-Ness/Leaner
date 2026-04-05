import Mathlib

variable {α β : Type*}

theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b := rfl

