import Mathlib

variable {α β : Type*}

theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b := rfl

