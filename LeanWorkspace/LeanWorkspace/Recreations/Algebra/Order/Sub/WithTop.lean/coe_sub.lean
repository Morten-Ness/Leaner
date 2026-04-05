import Mathlib

variable {α β : Type*}

variable [Sub α] [Bot α]

theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b := rfl

