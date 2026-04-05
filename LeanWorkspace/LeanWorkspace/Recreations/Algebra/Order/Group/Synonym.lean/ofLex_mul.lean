import Mathlib

variable {α β : Type*}

theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b := rfl

