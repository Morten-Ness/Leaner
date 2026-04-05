import Mathlib

variable {α β : Type*}

theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b := rfl

