import Mathlib

variable {α β : Type*}

theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b := rfl

