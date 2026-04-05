import Mathlib

variable {α β : Type*}

theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ := rfl

