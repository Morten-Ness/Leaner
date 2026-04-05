import Mathlib

variable {α β : Type*}

theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b := rfl

