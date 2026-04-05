import Mathlib

variable {α β : Type*}

theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b := rfl

